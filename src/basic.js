// Created by CuriousTorvald on 2020-05-19
// Version 1.0 Release Date 2020-12-28

/*
Copyright (c) 2020-2021 CuriousTorvald

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
 */

if (exec_args !== undefined && exec_args[1] !== undefined && exec_args[1].startsWith("-?")) {
    println("Usage: basic <optional path to basic program>");
    println("When the optional basic program is set, the interpreter will run the program and then quit if successful, remain open if the program had an error.");
    return 0;
}

const THEVERSION = "1.1-dev";

const PROD = false;
let INDEX_BASE = 0;
let TRACEON = (!PROD) && true;
let DBGON = (!PROD) && true;
let DATA_CURSOR = 0;
let DATA_CONSTS = [];
const DEFUNS_BUILD_DEFUNS = false;
const BASIC_HOME_PATH = "/home/basic/"
let replCmdBuf = []; // used to store "load filename" and issues it when user confirmed potential data loss
let replUsrConfirmed = false;

if (system.maxmem() < 8192) {
    println("Out of memory. BASIC requires 8K or more User RAM");
    throw Error("Out of memory");
}

let vmemsize = system.maxmem();

let cmdbuf = []; // index: line number
let gotoLabels = {};
let cmdbufMemFootPrint = 0;
let prompt = "Ok";
let prescan = false;

// lambdaBoundVars is used in two different mode:
//  - PARSER will just store a symbol as a string literal
//  - EXECUTOR will store the actual info of the bound vars in this format: [astType, astValue]
let lambdaBoundVars = []; // format: [[a,b],[c]] for "[c]~>[a,b]~>expr"

/* if an object can be FOR REAL cast to number */
function isNumable(s) {
    // array?
    if (Array.isArray(s)) return false;
    // undefined?
    if (s === undefined) return false;
    // null string?
    if (typeof s.trim == "function" && s.trim().length == 0) return false;
    // else?
    return !isNaN(s); // NOTE: isNaN('') == false
}
let tonum = (t) => t*1.0;
function cloneObject(o) { return JSON.parse(JSON.stringify(o)); }

class ParserError extends Error {
    constructor(...args) {
        super(...args);
        Error.captureStackTrace(this, ParserError);
    }
}

class InternalError extends Error {
    constructor(...args) {
        super(...args);
        Error.captureStackTrace(this, ParserError);
    }
}

let lang = {};
lang.badNumberFormat = Error("Illegal number format");
lang.badOperatorFormat = Error("Illegal operator format");
lang.divByZero = Error("Division by zero");
lang.badFunctionCallFormat = function(line, reason) {
    return Error("Illegal function call" + ((line) ? " in "+line : "") + ((reason) ? ": "+reason : ""));
};
lang.unmatchedBrackets = Error("Unmatched brackets");
lang.missingOperand = Error("Missing operand");
lang.noSuchFile = Error("No such file");
lang.outOfData = function(line) {
    return Error("Out of DATA"+(line !== undefined ? (" in "+line) : ""));
};
lang.nextWithoutFor = function(line, varname) {
    return Error("NEXT "+((varname !== undefined) ? ("'"+varname+"'") : "")+"without FOR in "+line);
};
lang.syntaxfehler = function(line, reason) {
    return Error("Syntax error" + ((line !== undefined) ? (" in "+line) : "") + ((reason !== undefined) ? (": "+reason) : ""));
};
lang.illegalType = function(line, obj) {
    return Error("Type mismatch" + ((obj !== undefined) ? ` "${obj} (typeof ${typeof obj})"` : "") + ((line !== undefined) ? (" in "+line) : ""));
 };
lang.refError = function(line, obj) {
    serial.printerr(`${line} Unresolved reference:`);
    serial.printerr(`    object: ${obj}, typeof: ${typeof obj}`);
    if (obj !== null && obj !== undefined) serial.printerr(`    entries: ${Object.entries(obj)}`);
    return Error("Unresolved reference" + ((obj !== undefined) ? ` "${obj}"` : "") + ((line !== undefined) ? (" in "+line) : ""));
};
lang.nowhereToReturn = function(line) { return "RETURN without GOSUB in " + line; };
lang.errorinline = function(line, stmt, errobj) {
    return Error('Error'+((line !== undefined) ? (" in "+line) : "")+' on "'+stmt+'": '+errobj);
};
lang.parserError = function(line, errorobj) {
    return Error("Parser error in " + line + ": " + errorobj);
};
lang.outOfMem = function(line) {
    return Error("Out of memory in " + line);
};
lang.dupDef = function(line, varname) {
    return Error("Duplicate definition"+((varname !== undefined) ? (" on "+varname) : "")+" in "+line);
};
lang.asgnOnConst = function(line, constname) {
    return Error('Trying to modify constant "'+constname+'" in '+line);
};
lang.subscrOutOfRng = function(line, object, index, maxlen) {
    return Error("Subscript out of range"+(object !== undefined ? (' for "'+object+'"') : '')+(index !== undefined ? (` (index: ${index}, len: ${maxlen})`) : "")+(line !== undefined ? (" in "+line) : ""));
};
lang.aG = " arguments were given";
lang.ord = function(n) {
    if (n % 10 == 1 && n % 100 != 11) return n+"st";
    if (n % 10 == 2 && n % 100 != 12) return n+"nd";
    if (n % 10 == 3 && n % 100 != 13) return n+"rd";
    return n+"th";
}
Object.freeze(lang);

let fs = {};
fs._close = function(portNo) {
    com.sendMessage(portNo, "CLOSE");
};
fs._flush = function(portNo) {
    com.sendMessage(portNo, "FLUSH");
};
// @return true if operation committed successfully, false if:
//             - opening file with R-mode and target file does not exists
//         throws if:
//             - java.lang.NullPointerException if path is null
//             - Error if operation mode is not "R", "W" nor "A"
fs.open = function(path, operationMode) {
    var port = _BIOS.FIRST_BOOTABLE_PORT;

    fs._flush(port[0]); fs._close(port[0]);

    var mode = operationMode.toUpperCase();
    if (mode != "R" && mode != "W" && mode != "A") {
        throw Error("Unknown file opening mode: " + mode);
    }

    com.sendMessage(port[0], "OPEN"+mode+'"'+BASIC_HOME_PATH+path+'",'+port[1]);
    let response = com.getStatusCode(port[0]);
    return (response == 0);
};
// @return the entire contents of the file in String
fs.readAll = function() {
    var port = _BIOS.FIRST_BOOTABLE_PORT;
    com.sendMessage(port[0], "READ");
    var response = com.getStatusCode(port[0]);
    if (135 == response) {
        throw Error("File not opened");
    }
    if (response < 0 || response >= 128) {
        throw Error("Reading a file failed with "+response);
    }
    return com.pullMessage(port[0]);
};
fs.write = function(string) {
    var port = _BIOS.FIRST_BOOTABLE_PORT;
    com.sendMessage(port[0], "WRITE"+string.length);
    var response = com.getStatusCode(port[0]);
    if (135 == response) {
        throw Error("File not opened");
    }
    if (response < 0 || response >= 128) {
        throw Error("Writing a file failed with "+response);
    }
    com.sendMessage(port[0], string);
    fs._flush(port[0]); fs._close(port[0]);
};
Object.freeze(fs);

// implement your own con object here
// requirements: reset_graphics(), getch(), curs_set(int), hitterminate(), resetkeybuf(), addch(int)

let getUsedMemSize = function() {
    var varsMemSize = 0;

    Object.entries(bS.vars).forEach((pair, i) => {
        var object = pair[1];

        if (Array.isArray(object)) {
            // TODO test 1-D array
            varsMemSize += object.length * 8;
        }
        else if (!isNaN(object)) varsMemSize += 8;
        else if (typeof object === "string" || object instanceof String) varsMemSize += object.length;
        else varsMemSize += 1;
    });
    return varsMemSize + cmdbufMemFootPrint; // + array's dimsize * 8 + variables' sizeof literal + functions' expression length
}

let reLineNum = /^[0-9]+ /;
//var reFloat = /^([\-+]?[0-9]*[.][0-9]+[eE]*[\-+0-9]*[fF]*|[\-+]?[0-9]+[.eEfF][0-9+\-]*[fF]?)$/;
//var reDec = /^([\-+]?[0-9_]+)$/;
//var reHex = /^(0[Xx][0-9A-Fa-f_]+)$/;
//var reBin = /^(0[Bb][01_]+)$/;

// must match partial
let reNumber = /([0-9]*[.][0-9]+[eE]*[\-+0-9]*[fF]*|[0-9]+[.eEfF][0-9+\-]*[fF]?)|([0-9]+(\_[0-9])*)|(0[Xx][0-9A-Fa-f_]+)|(0[Bb][01_]+)/;
//let reOps = /\^|;|\*|\/|\+|\-|[<>=]{1,2}/;

let reNum = /[0-9]+/;
let tbasexit = false;
const greetText = `Terran BASIC ${THEVERSION}  `+String.fromCharCode(179)+"  Scratchpad Memory: "+vmemsize+" bytes";
const greetLeftPad = (80 - greetText.length) >> 1;
const greetRightPad = 80 - greetLeftPad - greetText.length;

con.color_pair(0,253);
print(" ".repeat(greetLeftPad)+greetText+" ".repeat(greetRightPad));
con.color_pair(239,255);
println();
println(prompt);

// variable object constructor
/** variable object constructor
 * @param literal Javascript object or primitive
 * @type derived from JStoBASICtype + "usrdefun" + "internal_arrindexing_lazy" + "internal_assignment_object"
 * @see bS.builtin["="]
 */
let BasicVar = function(literal, type) {
    this.bvLiteral = literal;
    this.bvType = type;
}
// Abstract Syntax Tree
// creates empty tree node
let astToString = function(ast, depth, isFinalLeaf) {
    let l__ = "| ";
    
    let recDepth = depth || 0;
    if (!isAST(ast)) return "";
    
    let hastStr = ast.astHash;
    let sb = "";
    let marker = ("lit" == ast.astType) ? "i" :
                 ("op" == ast.astType) ? "+" :
                 ("string" == ast.astType) ? "@" :
                 ("num" == ast.astType) ? "$" :
                 ("array" == ast.astType) ? "[" :
                 ("defun_args" === ast.astType) ? "d" : "f";
    sb += l__.repeat(recDepth)+`${marker} ${ast.astLnum}: "${ast.astValue}" (astType:${ast.astType}); leaves: ${ast.astLeaves.length}; hash:"${hastStr}"\n`;    
    for (var k = 0; k < ast.astLeaves.length; k++) {
        sb += astToString(ast.astLeaves[k], recDepth + 1, k == ast.astLeaves.length - 1);
        if (ast.astSeps[k] !== undefined)
            sb += l__.repeat(recDepth)+` sep:${ast.astSeps[k]}\n`;
    }
    sb += l__.repeat(recDepth)+"`"+"-".repeat(22)+'\n';
    return sb;
}
let monadToString = function(monad, depth) {
    let recDepth = depth || 0;
    let l__ = "  ";
    let sb = ` M"${monad.mHash}"(${monad.mType}): `
    //if (monad.mType == "value") {
        sb += (monad.mVal === undefined) ? "(undefined)" : (isAST(monad.mVal)) ? `f"${monad.mVal.astHash}"` : (isMonad(monad.mVal)) ? `M"${monad.mVal.mHash}"` : monad.mVal;
    /*}
    else if (monad.mType == "list") {
        let elemToStr = function(e) {
            return (e === undefined) ? "(undefined)" :
                (isAST(e)) ? `f"${e.astHash}"` :
                (isMonad(e)) ? `M"${e.mHash}"` :
                e
        }
        
        let m = monad.mVal;
        while (1) {
            sb += elemToStr(m.p);
            if (m.n === undefined) break;
            else {
                sb += ",";
                m = m.n;
            }
        }
    }
    else {
        throw new InternalError("unknown monad subtype: "+m.mType);
    }*/
    return sb;
}
let theLambdaBoundVars = function() {
    let sb = "";
    lambdaBoundVars.forEach((it,i) => {
        if (i > 0) sb += ' |';
        sb += ` ${i} [`;
        it.forEach((it,i) => {
            if (i > 0) sb += ',';
            sb += `${it[0]}:${it[1]}`; // type and value pair
        });
        sb += ']';
    })
    return sb;
}
let makeBase32Hash = function() {
    let e = "YBNDRFG8EJKMCPQXOTLVWIS2A345H769";
    let m = e.length;
    return e[Math.floor(Math.random()*m)] + e[Math.floor(Math.random()*m)] + e[Math.floor(Math.random()*m)] + e[Math.floor(Math.random()*m)] + e[Math.floor(Math.random()*m)]
}
let BasicAST = function() {
    this.astLnum = 0;
    this.astLeaves = [];
    this.astSeps = [];
    this.astValue = undefined;
    this.astType = "null"; // lit, op, string, num, array, function, null, defun_args (! NOT usrdefun !)
    this.astHash = makeBase32Hash();
}
// I'm basically duck-typing here...
let isAST = (object) => (object === undefined) ? false : object.astLeaves !== undefined && object.astHash !== undefined
let isRunnable = (object) => isAST(object) || object.mType == "funseq";
let BasicFunSeq = function(f) {
    if (!Array.isArray(f) || !isAST(f[0])) throw new InternalError("Not an array of functions");
    this.mHash = makeBase32Hash();
    this.mType = "funseq";
    this.mVal = f;
}
/** A List Monad (a special case of Value-monad)
 * This monad MUST follow the monad law!
 * @param m a monadic value (Javascript array)
 */
let BasicListMonad = function(m) {
    this.mHash = makeBase32Hash();
    this.mType = "list";
    this.mVal = [m];
}
/** A Memoisation Monad, aka the most generic monad
 * This monad MUST follow the monad law!
 * @param m a monadic value
 */
/* Test this monad with following program
 * This program requires (>>=) to "play by the rules"
10 LSORT=[XS]~>IF LEN(XS)<1 THEN NIL ELSE LSORT(FILTER([K]~>K<HEAD XS,TAIL XS)) # HEAD(XS)!NIL # LSORT(FILTER([K]~>K>=HEAD XS,TAIL XS))
20 LREV=[XS]~>MAP([I]~>XS(I),LEN(XS)-1 TO 0 STEP -1)
30 LINC=[XS]~>MAP([I]~>I+1,XS)
40 L=7!9!4!5!2!3!1!8!6!NIL
100 MAGICKER=[XS]~>MRET(LSORT(XS))>>=([X]~>MRET(LREV(X))>>=([X]~>MRET(LINC(X))))
110 MAGICK_L = MAGICKER(L)
120 PRINT MAGICK_L()
 */
/* Value-monad satisfies monad laws, test with following program
10 F=[X]~>X*2 : G=[X]~>X^3 : RETN=[X]~>MRET(X)

100 PRINT:PRINT "First law: 'return a >>= k' equals to 'k a'"
110 K=[X]~>RETN(F(X)) : REM K is monad-returning function
120 A=42
130 KM=RETN(A)>>=K
140 KO=K(A)
150 PRINT("KM is ";TYPEOF(KM);", ";MEVAL(KM))
160 PRINT("KO is ";TYPEOF(KO);", ";MEVAL(KO))

200 PRINT:PRINT "Second law: 'm >>= return' equals to 'm'"
210 M=MRET(G(42))
220 MM=M>>=RETN
230 MO=M
240 PRINT("MM is ";TYPEOF(MM);", ";MEVAL(MM))
250 PRINT("MO is ";TYPEOF(MO);", ";MEVAL(MO))

300 PRINT:PRINT "Third law: 'm >>= (\x -> k x >>= h)' equals to '(m >>= k) >>= h'"
310 REM see line 110 for the definition of K
320 H=[X]~>RETN(G(X)) : REM H is monad-returning function
330 M=MRET(69)
340 M1=M>>=([X]~>K(X)>>=H)
350 M2=(M>>=K)>>=H
360 PRINT("M1 is ";TYPEOF(M1);", ";MEVAL(M1))
370 PRINT("M2 is ";TYPEOF(M2);", ";MEVAL(M2))
 */
let BasicMemoMonad = function(m) {
    this.mHash = makeBase32Hash();
    this.mType = "value";
    this.mVal = m; // a monadic value
    this.seq = undefined; // unused
}
// I'm basically duck-typing here...
let isMonad = (o) => (o === undefined) ? false : (o.mType !== undefined);

let literalTypes = ["string", "num", "bool", "array", "generator", "usrdefun", "monad"];
/*
@param variable SyntaxTreeReturnObj, of which  the 'troType' is defined in BasicAST.
@return a value, if the input type if string or number, its literal value will be returned. Otherwise will search the
        BASIC variable table and return the literal value of the BasicVar; undefined will be returned if no such var exists.
*/
let resolve = function(variable) {
    if (variable === undefined) return undefined;
    // head error checking
    if (variable.troType === undefined) {
        // primitves types somehow injected from elsewhere (main culprit: MAP)
        //throw Error(`BasicIntpError: trying to resolve unknown object '${variable}' with entries ${Object.entries(variable)}`);

        if (isNumable(variable)) return tonum(variable);
        if (Array.isArray(variable)) return variable;
        if (isGenerator(variable) || isAST(variable) || isMonad(variable)) return variable;
        if (typeof variable == "object")
            throw Error(`BasicIntpError: trying to resolve unknown object '${variable}' with entries ${Object.entries(variable)}`);
        return variable;
    }
    else if (variable.troType === "internal_arrindexing_lazy")
        return eval("variable.troValue.arrFull"+variable.troValue.arrKey);
    else if (literalTypes.includes(variable.troType) || variable.troType.startsWith("internal_"))
        return variable.troValue;
    else if (variable.troType == "lit") {
        // when program tries to call builtin function (e.g. SIN), return usrdefun-wrapped version
        if (bS.builtin[variable.troValue] !== undefined) {
            return bS.wrapBuiltinToUsrdefun(variable.troValue);
        }
        // else, it's just a plain-old variable :p
        else {
            let basicVar = bS.vars[variable.troValue];
            if (basicVar === undefined) throw lang.refError(undefined, variable.troValue);
            if (basicVar.bvLiteral === "") return "";
            return (basicVar !== undefined) ? basicVar.bvLiteral : undefined;
        }
    }
    else if (variable.troType == "null")
        return undefined;
    // tail error checking
    else
        throw Error("BasicIntpError: unknown variable/object with type "+variable.troType+", with value "+variable.troValue);
}
let findHighestIndex = function(exprTree) {
    let highestIndex = [-1,-1];
    // look for the highest index of [a,b]
    let rec = function(exprTree) {
        bF._recurseApplyAST(exprTree, it => {
            if (it.astType == "defun_args") {
                let recIndex = it.astValue[0];
                let ordIndex = it.astValue[1];
                
                if (recIndex > highestIndex[0]) {
                    highestIndex = [recIndex, 0];
                }
                
                if (recIndex == highestIndex[0] && ordIndex > highestIndex[1]) {
                    highestIndex[1] = ordIndex;
                }
            }
            else if (isAST(it.astValue)) {
                rec(it.astValue);
            }
        });
    };rec(exprTree);
    return highestIndex;
}
let indexDec = function(node, recIndex) {
    if (node.astType == "defun_args" && node.astValue[0] === recIndex) {
        let newNode = cloneObject(node);
        newNode.astValue[1] -= 1;
        return newNode;
    }
    else return node;
}
let curryDefun = function(inputTree, inputValue) {    
    let exprTree = cloneObject(inputTree);
    let value = cloneObject(inputValue);
    let highestIndex = findHighestIndex(exprTree)[0];
    
    if (DBGON) {
        serial.println("[curryDefun] highest index to curry: "+highestIndex);
    }
    
    let substitution = new BasicAST();
    if (isAST(value)) {
        substitution = value;
    }
    else {
        substitution.astLnum = "??";
        substitution.astType = JStoBASICtype(value);
        substitution.astValue = value;
    }
    
    // substitute the highest index with given value
    /*bF._recurseApplyAST(exprTree, it => {
        return (it.astType == "defun_args" && it.astValue[0] === highestIndex[0] && it.astValue[1] === highestIndex[1]) ? substitution : it
    });*/
    
    // substitute the highest index [max recIndex, 0] with given value
    // and if recIndex is same as the highestIndex and ordIndex is greater than zero,
    // decrement the ordIndex
    bF._recurseApplyAST(exprTree, it => {
        return (it.astType == "defun_args" && it.astValue[0] === highestIndex && it.astValue[1] === 0) ? substitution : indexDec(it, highestIndex)
    });
    
    return exprTree;
}
let getMonadEvalFun = (monad) => function(lnum, stmtnum, args, sep) {
    if (!isMonad(monad)) throw lang.badFunctionCallFormat(lnum, "not a monad");
        
    if (DBGON) {
        serial.println("[BASIC.MONADEVAL] monad:");
        serial.println(monadToString(monad));
    }
    
    if (monad.mType == "funseq") {
        let arg = args[0];
        monad.mVal.forEach(f => {
            arg = bS.getDefunThunk(f)(lnum, stmtnum, [arg]);
        })
        return arg;
    }
    else {
        // args are futile
        return monad.mVal;
    }
}
let listMonConcat = function(parentm, childm) {
    parentm.mVal = parentm.mVal.concat(childm.mVal);
    return parentm;
}
let countArgs = function(defunTree) {
    let cnt = -1;
    bF._recurseApplyAST(defunTree, it => {
        if (it.astType == "defun_args" && it.astValue > cnt)
            cnt = it.astValue;
    });
    
    return cnt+1;
}
let argCheckErr = function(lnum, o) {
    if (o === undefined) throw lang.refError(lnum, "(variable is undefined)");
    if (o.troType == "null") throw lang.refError(lnum, o);
    if (o.troType == "lit" && bS.builtin[o.troValue] !== undefined) return;
    if (o.troType == "lit" && bS.vars[o.troValue] === undefined) throw lang.refError(lnum, o.troValue);
}
let oneArg = function(lnum, stmtnum, args, action) {
    if (args.length != 1) throw lang.syntaxfehler(lnum, args.length+lang.aG);
    argCheckErr(lnum, args[0]);
    var rsvArg0 = resolve(args[0]);
    return action(rsvArg0);
}
let oneArgNul = function(lnum, stmtnum, args, action) {
    if (args.length != 1) throw lang.syntaxfehler(lnum, args.length+lang.aG);
    var rsvArg0 = resolve(args[0]);
    return action(rsvArg0);
}
let oneArgNum = function(lnum, stmtnum, args, action) {
    if (args.length != 1) throw lang.syntaxfehler(lnum, args.length+lang.aG);
    argCheckErr(lnum, args[0]);
    var rsvArg0 = resolve(args[0]);
    if (isNaN(rsvArg0)) throw lang.illegalType(lnum, args[0]);
    return action(rsvArg0);
}
let twoArg = function(lnum, stmtnum, args, action) {
    if (args.length != 2) throw lang.syntaxfehler(lnum, args.length+lang.aG);
    argCheckErr(lnum, args[0]);
    var rsvArg0 = resolve(args[0]);
    argCheckErr(lnum, args[1]);
    var rsvArg1 = resolve(args[1]);
    return action(rsvArg0, rsvArg1);
}
let twoArgNul = function(lnum, stmtnum, args, action) {
    if (args.length != 2) throw lang.syntaxfehler(lnum, args.length+lang.aG);
    var rsvArg0 = resolve(args[0]);
    var rsvArg1 = resolve(args[1]);
    return action(rsvArg0, rsvArg1);
}
let twoArgNum = function(lnum, stmtnum, args, action) {
    if (args.length != 2) throw lang.syntaxfehler(lnum, args.length+lang.aG);
    argCheckErr(lnum, args[0]);
    var rsvArg0 = resolve(args[0]);
    if (isNaN(rsvArg0)) throw lang.illegalType(lnum, "LH:"+Object.entries(args[0]));
    argCheckErr(lnum, args[1]);
    var rsvArg1 = resolve(args[1]);
    if (isNaN(rsvArg1)) throw lang.illegalType(lnum, "RH:"+Object.entries(args[1]));
    return action(rsvArg0, rsvArg1);
}
let threeArg = function(lnum, stmtnum, args, action) {
    if (args.length != 3) throw lang.syntaxfehler(lnum, args.length+lang.aG);
    argCheckErr(lnum, args[0]);
    var rsvArg0 = resolve(args[0]);
    argCheckErr(lnum, args[1]);
    var rsvArg1 = resolve(args[1]);
    argCheckErr(lnum, args[2]);
    var rsvArg2 = resolve(args[2]);
    return action(rsvArg0, rsvArg1, rsvArg2);
}
let threeArgNum = function(lnum, stmtnum, args, action) {
    if (args.length != 3) throw lang.syntaxfehler(lnum, args.length+lang.aG);
    if (rsvArg0 === undefined) throw lang.refError(lnum, args[0]);
    argCheckErr(lnum, args[0]);
    if (isNaN(rsvArg0)) throw lang.illegalType(lnum, args[0]);
    if (rsvArg1 === undefined) throw lang.refError(lnum, args[1]);
    argCheckErr(lnum, args[1]);
    if (isNaN(rsvArg1)) throw lang.illegalType(lnum, args[1]);
    if (rsvArg2 === undefined) throw lang.refError(lnum, args[2]);
    argCheckErr(lnum, args[2]);
    if (isNaN(rsvArg2)) throw lang.illegalType(lnum, args[2]);
    return action(rsvArg0, rsvArg1, rsvArg2);
}
let varArg = function(lnum, stmtnum, args, action) {
    var rsvArg = args.map((it) => {
        argCheckErr(lnum, it);
        var r = resolve(it);
        return r;
    });
    return action(rsvArg);
}
let varArgNum = function(lnum, stmtnum, args, action) {
    var rsvArg = args.map((it) => {
        argCheckErr(lnum, it);
        var r = resolve(it);
        if (isNaN(r)) throw lang.illegalType(lnum, r);
        return r;
    });
    return action(rsvArg);
}
let makeIdFun = () => {
    let i = new BasicAST();
    i.astValue = [0,0];
    i.astType = "defun_args";
    i.astLnum = "**";
    
    let a = new BasicAST();
    a.astValue = i;
    a.astType = "usrdefun";
    a.astLnum = "**";
    
    return a;
}
let _basicConsts = {
   "NIL": new BasicVar([], "array"),
   "PI": new BasicVar(Math.PI, "num"),
   "TAU": new BasicVar(Math.PI * 2.0, "num"),
   "EULER": new BasicVar(Math.E, "num"),
   "ID": new BasicVar(makeIdFun(), "usrdefun"),
   "UNDEFINED": new BasicVar(undefined, "null"),
   "TRUE": new BasicVar(true, "bool"),
   "FALSE": new BasicVar(false, "bool")
};
Object.freeze(_basicConsts);
let initBvars = function() {
    return cloneObject(_basicConsts);
}
let ForGen = function(s,e,t) {
    this.start = s;
    this.end = e;
    this.step = t || 1;

    this.current = this.start;
    this.stepsgn = (this.step > 0) ? 1 : -1;
}
// I'm basically duck-typing here...
let isGenerator = (o) => o.start !== undefined && o.end !== undefined && o.step !== undefined && o.stepsgn !== undefined
let genToArray = (gen) => {
    let a = [];
    let cur = gen.start;
    while (cur*gen.stepsgn + gen.step*gen.stepsgn <= (gen.end + gen.step)*gen.stepsgn) {
        a.push(cur);
        cur += gen.step;
    }
    return a;
}
let genHasHext = (o) => o.current*o.stepsgn + o.step*o.stepsgn <= (o.end + o.step)*o.stepsgn;
let genGetNext = (gen, mutated) => {
    //if (mutated === undefined) throw "InternalError: parameter is missing";
    if (mutated !== undefined) gen.current = (mutated|0);
    gen.current += gen.step;
    //serial.println(`[BASIC.FORGEN] ${(mutated|0)} -> ${gen.current}`);
    return genHasHext(gen) ? gen.current : undefined;
}
let genToString = (gen) => `Generator: ${gen.start} to ${gen.end}`+((gen.step !== 1) ? ` step ${gen.step}` : '');
let genReset = (gen) => { gen.current = gen.start }
let bS = {}; // BASIC status
bS.gosubStack = [];
bS.forLnums = {}; // key: forVar, value: [lnum, stmtnum]
bS.forStack = []; // forVars only
bS.vars = initBvars(); // contains instances of BasicVars
bS.rnd = 0; // stores mantissa (23 bits long) of single precision floating point number
bS.getDimSize = function(array, dim) {
    var dims = [];
    while (true) {
        dims.push(array.length);

        if (Array.isArray(array[0]))
            array = array[0];
        else
            break;
    }
    return dims[dim];
};
bS.getArrayIndexFun = function(lnum, stmtnum, arrayName, array) {
    if (lnum === undefined || stmtnum === undefined) throw Error(`Line or statement number is undefined: (${lnum},${stmtnum})`);

    return function(lnum, stmtnum, args, seps) {
        if (lnum === undefined || stmtnum === undefined) throw Error(`Line or statement number is undefined: (${lnum},${stmtnum})`);

        return varArgNum(lnum, stmtnum, args, (dims) => {
            if (TRACEON) serial.println("ar dims: "+dims);

            let dimcnt = 1;
            let oldIndexingStr = "";
            let indexingstr = "";
            
            dims.forEach(d => {
                oldIndexingStr = indexingstr;
                indexingstr += `[${d-INDEX_BASE}]`;

                var testingArr = eval(`array${indexingstr}`);
                if (testingArr === undefined)
                    throw lang.subscrOutOfRng(lnum, `${arrayName}${oldIndexingStr} (${lang.ord(dimcnt)} dim)`, d-INDEX_BASE, bS.getDimSize(array, dimcnt-1));

                dimcnt += 1;
            });

            if (TRACEON)
                serial.println("ar indexedValue = "+`/*ar1*/array${indexingstr}`);

            return {arrFull: array, arrName: arrayName, arrKey: indexingstr};
        });
    };
};
/**
 * @return a Javascript function that when called, evaluates the exprTree
 */
bS.getDefunThunk = function(exprTree, norename) {
    if (!isRunnable(exprTree)) throw new InternalError("not a syntax tree");
    
    // turns funseq-monad into runnable function
    if (isMonad(exprTree)) return getMonadEvalFun(exprTree);
    
    let tree = cloneObject(exprTree); // ALWAYS create new tree instance!
    
    return function(lnum, stmtnum, args, seps) {
        if (lnum === undefined || stmtnum === undefined) throw Error(`Line or statement number is undefined: (${lnum},${stmtnum})`);
        
        if (!norename) {
            let argsMap = args.map(it => {
                //argCheckErr(lnum, it);
                let rit = resolve(it);
                return [JStoBASICtype(rit), rit]; // substitute for [astType, astValue]
            });//.reverse();
            
            // bind arguments
            lambdaBoundVars.unshift(argsMap);
            
            if (DBGON) {
                serial.println("[BASIC.getDefunThunk.invoke] unthunking: ");
                serial.println(astToString(tree));
                serial.println("[BASIC.getDefunThunk.invoke] thunk args:");
                serial.println(argsMap);
                serial.println("[BASIC.getDefunThunk.invoke] lambda bound vars:");
                serial.println(theLambdaBoundVars());
            }
            
            // perform renaming
            bF._recurseApplyAST(tree, (it) => {
                if ("defun_args" == it.astType) {
                    if (DBGON) {
                        serial.println("[BASIC.getDefunThunk.invoke] thunk renaming arg-tree branch:");
                        serial.println(astToString(it));
                    }
                    
                    let recIndex = it.astValue[0];
                    let argIndex = it.astValue[1];
                    
                    let theArg = lambdaBoundVars[recIndex][argIndex]; // instanceof theArg == resolved version of SyntaxTreeReturnObj
                    
                    if (theArg !== undefined) { // this "forgiveness" is required to implement currying
                        if (DBGON) {
                            serial.println("[BASIC.getDefunThunk.invoke] thunk renaming-theArg: "+theArg);
                            serial.println(`${Object.entries(theArg)}`);
                        }
                        
                        if (theArg[0] === "null") {
                            throw new InternalError(`Bound variable is ${theArg}; lambdaBoundVars: ${theLambdaBoundVars()}`);
                        }
                        
                        it.astValue = theArg[1];
                        it.astType = theArg[0];
                    }
                    
                    if (DBGON) {
                        serial.println("[BASIC.getDefunThunk.invoke] thunk successfully renamed arg-tree branch:");
                        serial.println(astToString(it));
                    }
                }
            });
            
            if (DBGON) {
                serial.println("[BASIC.getDefunThunk.invoke] resulting thunk tree:");
                serial.println(astToString(tree));
            }
        }
        else {
            if (DBGON) {
                serial.println("[BASIC.getDefunThunk.invoke] no rename, resulting thunk tree:");
                serial.println(astToString(tree));
            }
        }
        
        // evaluate new tree
        if (DBGON) {
            serial.println("[BASIC.getDefunThunk.invoke] evaluating tree:");
        }
        let ret = resolve(bF._executeSyntaxTree(lnum, stmtnum, tree, 0));
        
        // unbind previously bound arguments
        if (!norename) {
            lambdaBoundVars.shift();
        }
        
        return ret;
    }
};
bS.wrapBuiltinToUsrdefun = function(funcname) {
    let argCount = bS.builtin[funcname].argc;
    
    if (argCount === undefined) throw new InternalError(`${funcname} cannot be wrapped into usrdefun`);
    
    let leaves = [];
    for (let k = 0; k < argCount; k++) {
        let l = new BasicAST();
        l.astLnum = "**";
        l.astValue = [0,k];
        l.astType = "defun_args";
        
        leaves.push(l);
    }
    
    let tree = new BasicAST();
    tree.astLnum = "**";
    tree.astValue = funcname;
    tree.astType = "function";
    tree.astLeaves = leaves;
    
    return tree;
}
/* Accepts troValue, assignes to BASIC variable, and returns internal_assign_object
 * @params troValue Variable to assign into
 * @params rh the value, resolved
 */
bS.addAsBasicVar = function(lnum, troValue, rh) {
    if (troValue.arrFull !== undefined) { // assign to existing array
        if (Array.isArray(rh)) throw lang.illegalType(lnum, rh); // no ragged array!
        let arr = eval("troValue.arrFull"+troValue.arrKey);
        if (Array.isArray(arr)) throw lang.subscrOutOfRng(lnum, arr);
        eval("troValue.arrFull"+troValue.arrKey+"=rh");
        return {asgnVarName: troValue.arrName, asgnValue: rh};
    }
    else {
        let varname = troValue.toUpperCase();
        //println("input varname: "+varname);
        if (_basicConsts[varname]) throw lang.asgnOnConst(lnum, varname);
        let type = JStoBASICtype(rh);
        bS.vars[varname] = new BasicVar(rh, type);
        return {asgnVarName: varname, asgnValue: rh};
    }
}
bS.builtin = {
/*
@param lnum line number
@param args instance of the SyntaxTreeReturnObj

if no args were given (e.g. "10 NEXT()"), args[0] will be: {troType: null, troValue: , troNextLine: 11}
if no arg text were given (e.g. "10 NEXT"), args will have zero length
*/
"=" : {argc:2, f:function(lnum, stmtnum, args) {
    if (args.length != 2) throw lang.syntaxfehler(lnum, args.length+lang.aG);
    var troValue = args[0].troValue;

    var rh = resolve(args[1]);
    if (rh === undefined) throw lang.refError(lnum, "RH:"+args[1].troValue);

    if (isNumable(rh)) rh = tonum(rh) // if string we got can be cast to number, do it

    //println(lnum+" = lh: "+Object.entries(args[0]));
    //println(lnum+" = rh raw: "+Object.entries(args[1]));
    //println(lnum+" = rh resolved: "+rh);
    //try { println(lnum+" = rh resolved entries: "+Object.entries(rh)); }
    //catch (_) {}

    return bS.addAsBasicVar(lnum, troValue, rh);
}},
"IN" : {argc:2, f:function(lnum, stmtnum, args) { // almost same as =, but don't actually make new variable. Used by FOR statement
    if (args.length != 2) throw lang.syntaxfehler(lnum, args.length+lang.aG);
    var troValue = args[0].troValue;

    var rh = resolve(args[1]);
    if (rh === undefined) throw lang.refError(lnum, "RH:"+args[1].troValue);

    if (troValue.arrFull !== undefined) {
        throw lang.syntaxfehler(lnum);
    }
    else {
        var varname = troValue.toUpperCase();
        var type = JStoBASICtype(rh);
        if (_basicConsts[varname]) throw lang.asgnOnConst(lnum, varname);
        return {asgnVarName: varname, asgnValue: rh};
    }
}},
"==" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArgNul(lnum, stmtnum, args, (lh,rh) => lh == rh);
}},
"<>" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (lh,rh) => lh != rh);
}},
"><" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (lh,rh) => lh != rh);
}},
"<=" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh <= rh);
}},
"=<" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh <= rh);
}},
">=" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh >= rh);
}},
"=>" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh >= rh);
}},
"<" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh < rh);
}},
">" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh > rh);
}},
"<<" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh << rh);
}},
">>" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh >>> rh);
}},
"UNARYMINUS" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => -lh);
}},
"UNARYPLUS" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => +lh);
}},
"UNARYLOGICNOT" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => !(lh));
}},
"UNARYBNOT" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => ~(lh));
}},
"BAND" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh & rh);
}},
"BOR" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh | rh);
}},
"BXOR" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh ^ rh);
}},
"!" : {argc:2, f:function(lnum, stmtnum, args) { // Haskell-style CONS
    return twoArg(lnum, stmtnum, args, (lh,rh) => {
        if (Array.isArray(rh) && Array.isArray(lh))
            throw lang.illegalType(lnum, lh); // NO ragged array for BASIC array!
        
        if (Array.isArray(rh)) {
            return [lh].concat(rh);
        }
        else if (rh.mType === "list") {
            rh.mVal = [lh].concat(rh.mVal);
            return rh;
        }
        else throw lang.illegalType(lnum, rh);
    });
}},
"~" : {argc:2, f:function(lnum, stmtnum, args) { // array PUSH
    return twoArg(lnum, stmtnum, args, (lh,rh) => {
        if (Array.isArray(lh) && Array.isArray(rh))
            throw lang.illegalType(lnum, rh); // NO ragged array for BASIC array!
        
        if (Array.isArray(lh)) {
            return lh.concat([rh]);
        }
        else if (lh.mType === "list") {
            lh.mVal = [lh.mVal].concat([rh]);
            return lh;
        }
        else throw lang.illegalType(lnum, lh);
    });
}},
"#" : {argc:2, f:function(lnum, stmtnum, args) { // array CONCAT
    return twoArg(lnum, stmtnum, args, (lh,rh) => {
        if (Array.isArray(lh) && Array.isArray(rh)) {
            return lh.concat(rh);
        }
        else if (lh.mType == "list" && rh.mType == "list") {
            let newMval = lh.mVal.concat(rh.mVal);
            return new BasicListMonad(newMval);
        }
        else
            throw lang.illegalType(lnum);
    });
}},
"+" : {argc:2, f:function(lnum, stmtnum, args) { // addition, string concat
    return twoArg(lnum, stmtnum, args, (lh,rh) => (!isNaN(lh) && !isNaN(rh)) ? (tonum(lh) + tonum(rh)) : (lh + rh));
}},
"-" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh - rh);
}},
"*" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh * rh);
}},
"/" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => {
        if (rh == 0) throw lang.divByZero;
        return lh / rh;
    });
}},
"\\" : {argc:2, f:function(lnum, stmtnum, args) { // integer division, rounded towards zero
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => {
        if (rh == 0) throw lang.divByZero;
        return (lh / rh)|0;
    });
}},
"MOD" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => {
        if (rh == 0) throw lang.divByZero;
        return lh % rh;
    });
}},
"^" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => {
        let r = Math.pow(lh, rh);
        if (isNaN(r)) throw lang.badFunctionCallFormat(lnum);
        if (!isFinite(r)) throw lang.divByZero;
        return r;
    });
}},
"TO" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (from, to) => new ForGen(from, to, 1));
}},
"STEP" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (gen, step) => {
        if (!isGenerator(gen)) throw lang.illegalType(lnum, gen);
        return new ForGen(gen.start, gen.end, step);
    });
}},
"DIM" : {f:function(lnum, stmtnum, args) {
    return varArgNum(lnum, stmtnum, args, (revdims) => {
        let dims = revdims.reverse();
        let arraydec = "Array(dims[0]).fill(0)";
        for (let k = 1; k < dims.length; k++) {
            arraydec = `Array(dims[${k}]).fill().map(_=>${arraydec})`
        }
        return eval(arraydec);
    });
}},
"PRINT" : {argc:1, f:function(lnum, stmtnum, args, seps) {
    if (args.length == 0)
        println();
    else {
        for (var llll = 0; llll < args.length; llll++) {
            // parse separators.
            // ; - concat
            // , - tab
            if (llll >= 1) {
                if (seps[llll - 1] == ",") print("\t");
            }

            var rsvArg = resolve(args[llll]);
            //if (rsvArg === undefined && args[llll] !== undefined && args[llll].troType != "null") throw lang.refError(lnum, args[llll].troValue);

            //serial.println(`${lnum} PRINT ${lang.ord(llll)} arg: ${Object.entries(args[llll])}, resolved: ${rsvArg}`);

            let printstr = "";
            if (rsvArg === undefined || rsvArg === "")
                printstr = "";
            else if (rsvArg.toString !== undefined)
                printstr = rsvArg.toString();
            else
                printstr = rsvArg;

            print(printstr);
            if (TRACEON) serial.println("[BASIC.PRINT] "+printstr);
        }
    }

    if (args[args.length - 1] !== undefined && args[args.length - 1].troType != "null") println();
}},
"EMIT" : {argc:1, f:function(lnum, stmtnum, args, seps) {
    if (args.length == 0)
        println();
    else {
        for (var llll = 0; llll < args.length; llll++) {
            // parse separators.
            // ; - concat
            // , - tab
            if (llll >= 1) {
                if (seps[llll - 1] == ",") print("\t");
            }

            var rsvArg = resolve(args[llll]);
            if (rsvArg === undefined && args[llll] !== undefined && args[llll].troType != "null") throw lang.refError(lnum, args[llll].troValue);

            let printstr = "";
            if (rsvArg === undefined)
                print("")
            else if (!isNaN(rsvArg)) {
                let c = con.getyx();
                con.addch(rsvArg);
            }
            else if (rsvArg.toString !== undefined)
                print(rsvArg.toString());
            else
                printstr = (rsvArg);

            if (TRACEON) serial.println("[BASIC.EMIT] "+printstr);
        }
    }

    if (args[args.length - 1] !== undefined && args[args.length - 1].troType != "null") println();
}},
"POKE" : {argc:2, f:function(lnum, stmtnum, args) {
    twoArgNum(lnum, stmtnum, args, (lh,rh) => sys.poke(lh, rh));
}},
"PEEK" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => sys.peek(lh));
}},
"GOTO" : {argc:1, f:function(lnum, stmtnum, args) {
    // search from gotoLabels first
    let line = gotoLabels[args[0].troValue];
    // if not found, use resolved variable
    if (line === undefined) line = resolve(args[0]);
    if (line < 0) throw lang.syntaxfehler(lnum, line);

    return new JumpObj(line, 0, lnum, line);
}},
"GOSUB" : {argc:1, f:function(lnum, stmtnum, args) {
    // search from gotoLabels first
    let line = gotoLabels[args[0].troValue];
    // if not found, use resolved variable
    if (line === undefined) line = resolve(args[0]);
    if (line < 0) throw lang.syntaxfehler(lnum, line);

    bS.gosubStack.push([lnum, stmtnum + 1]);
    //println(lnum+" GOSUB into "+lh);
    return new JumpObj(line, 0, lnum, line);
}},
"RETURN" : {f:function(lnum, stmtnum, args) {
    var r = bS.gosubStack.pop();
    if (r === undefined) throw lang.nowhereToReturn(lnum);
    //println(lnum+" RETURN to "+r);
    return new JumpObj(r[0], r[1], lnum, r);
}},
"CLEAR" : {argc:0, f:function(lnum, stmtnum, args) {
    bS.vars = initBvars();
}},
"PLOT" : {argc:3, f:function(lnum, stmtnum, args) {
    threeArgNum(lnum, stmtnum, args, (xpos, ypos, color) => graphics.plotPixel(xpos, ypos, color));
}},
"AND" : {argc:2, f:function(lnum, stmtnum, args) {
    if (args.length != 2) throw lang.syntaxfehler(lnum, args.length+lang.aG);
    var rsvArg = args.map((it) => resolve(it));
    rsvArg.forEach((v) => {
        if (v === undefined) throw lang.refError(lnum, v);
        if (typeof v !== "boolean") throw lang.illegalType(lnum, v);
    });
    var argum = rsvArg.map((it) => {
        if (it === undefined) throw lang.refError(lnum, it);
        return it;
    });
    return argum[0] && argum[1];
}},
"OR" : {argc:2, f:function(lnum, stmtnum, args) {
    if (args.length != 2) throw lang.syntaxfehler(lnum, args.length+lang.aG);
    var rsvArg = args.map((it) => resolve(it));
    rsvArg.forEach((v) => {
        if (v === undefined) throw lang.refError(lnum, v.value);
        if (typeof v !== "boolean") throw lang.illegalType(lnum, v);
    });
    var argum = rsvArg.map((it) => {
        if (it === undefined) throw lang.refError(lnum, it);
        return it;
    });
    return argum[0] || argum[1];
}},
"RND" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => {
        if (!(args.length > 0 && args[0].troValue === 0))
            bS.rnd = Math.random();//(bS.rnd * 214013 + 2531011) % 16777216; // GW-BASIC does this
        return bS.rnd;
    });
}},
"ROUND" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => Math.round(lh));
}},
"FLOOR" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => Math.floor(lh));
}},
"INT" : {argc:1, f:function(lnum, stmtnum, args) { // synonymous to FLOOR
    return oneArgNum(lnum, stmtnum, args, (lh) => Math.floor(lh));
}},
"CEIL" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => Math.ceil(lh));
}},
"FIX" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => (lh|0));
}},
"CHR" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => String.fromCharCode(lh));
}},
"TEST" : {argc:1, f:function(lnum, stmtnum, args) {
    if (args.length != 1) throw lang.syntaxfehler(lnum, args.length+lang.aG);
    return resolve(args[0]);
}},
"FOREACH" : {f:function(lnum, stmtnum, args) { // list comprehension model
    var asgnObj = resolve(args[0]);
    // type check
    if (asgnObj === undefined) throw lang.syntaxfehler(lnum);
    if (!Array.isArray(asgnObj.asgnValue)) throw lang.illegalType(lnum, asgnObj);

    var varname = asgnObj.asgnVarName;

    // assign new variable
    // the var itself will have head of the array, and the head itself will be removed from the array
    bS.vars[varname] = new BasicVar(asgnObj.asgnValue[0], JStoBASICtype(asgnObj.asgnValue.shift()));
    // stores entire array (sans head) into temporary storage
    bS.vars["for var "+varname] = new BasicVar(asgnObj.asgnValue, "array");
    // put the varname to forstack
    bS.forLnums[varname] = [lnum, stmtnum];
    bS.forStack.push(varname);
}},
"FOR" : {f:function(lnum, stmtnum, args) { // generator model
    var asgnObj = resolve(args[0]);
    // type check
    if (asgnObj === undefined) throw lang.syntaxfehler(lnum);
    if (!isGenerator(asgnObj.asgnValue)) throw lang.illegalType(lnum, typeof asgnObj);

    var varname = asgnObj.asgnVarName;
    var generator = asgnObj.asgnValue;

    // assign new variable
    // the var itself will have head of the array, and the head itself will be removed from the array
    bS.vars[varname] = new BasicVar(generator.start, "num");
    // stores entire array (sans head) into temporary storage
    bS.vars["for var "+varname] = new BasicVar(generator, "generator");
    // put the varname to forstack
    bS.forLnums[varname] = [lnum, stmtnum];
    bS.forStack.push(varname);
}},
"NEXT" : {f:function(lnum, stmtnum, args) {
    // if no args were given
    if (args.length == 0 || (args.length == 1 && args.troType == "null")) {
        // go to most recent FOR
        var forVarname = bS.forStack.pop();
        //serial.println(lnum+" NEXT > forVarname = "+forVarname);
        if (forVarname === undefined) {
            throw lang.nextWithoutFor(lnum);
        }

        if (TRACEON) serial.println("[BASIC.FOR] looping "+forVarname);

        var forVar = bS.vars["for var "+forVarname].bvLiteral;

        if (isGenerator(forVar))
            bS.vars[forVarname].bvLiteral = genGetNext(forVar, bS.vars[forVarname].bvLiteral);
        else
            bS.vars[forVarname].bvLiteral = forVar.shift();

        if ((bS.vars[forVarname].bvLiteral !== undefined)) {
            // feed popped value back, we're not done yet
            bS.forStack.push(forVarname);
            let forLnum = bS.forLnums[forVarname]
            return new JumpObj(forLnum[0], forLnum[1]+1, lnum, [forLnum[0], forLnum[1]+1]); // goto the statement RIGHT AFTER the FOR-declaration
        }
        else {
            if (isGenerator(forVar))
                bS.vars[forVarname].bvLiteral = forVar.current; // true BASIC compatibility for generator
            else
                bS.vars[forVarname] === undefined; // unregister the variable

            return new JumpObj(lnum, stmtnum + 1, lnum, [lnum, stmtnum + 1]);
        }
    }

    throw lang.syntaxfehler(lnum, "extra arguments for NEXT");
}},
/*
10 input;"what is your name";a$

£ Line 10 (function)
| leaves: 3
| value: input (type: string)
£ Line 0 (null)
| leaves: 0
| value: undefined (type: undefined)
`-----------------
|  ;
| ¶ Line 10 (string)
| | leaves: 0
| | value: what is your name (type: string)
| `-----------------
|  ;
| i Line 10 (literal)
| | leaves: 0
| | value: A$ (type: string)
| `-----------------
`-----------------
10 input "what is your name";a$

£ Line 10 (function)
| leaves: 2
| value: input (type: string)
| ¶ Line 10 (string)
| | leaves: 0
| | value: what is your name (type: string)
| `-----------------
|  ;
| i Line 10 (literal)
| | leaves: 0
| | value: A$ (type: string)
| `-----------------
`-----------------
*/
"INPUT" : {argc:1, f:function(lnum, stmtnum, args) {
    if (args.length != 1) throw lang.syntaxfehler(lnum, args.length+lang.aG);
    let troValue = args[0].troValue;

    // print out prompt text
    print("? "); var rh = sys.read().trim();

    // if string we got can be cast to number, do it
    // NOTE: empty string will be cast to 0, which corresponds to GW-BASIC
    if (!isNaN(rh)) rh = tonum(rh)

    return bS.addAsBasicVar(lnum, troValue, rh);
}},
"CIN" : {argc:0, f:function(lnum, stmtnum, args) {
    return sys.read().trim();
}},
"END" : {argc:0, f:function(lnum, stmtnum, args) {
    serial.println("Program terminated in "+lnum);
    return new JumpObj(Number.MAX_SAFE_INTEGER, Number.MAX_SAFE_INTEGER - 1, lnum, undefined); // GOTO far-far-away
}},
"SPC" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => " ".repeat(lh));
}},
"LEFT" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (str, len) => str.substring(0, len));
}},
"MID" : {argc:3, f:function(lnum, stmtnum, args) {
    return threeArg(lnum, stmtnum, args, (str, start, len) => str.substring(start-INDEX_BASE, start-INDEX_BASE+len));
}},
"RIGHT" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (str, len) => str.substring(str.length - len, str.length));
}},
"SGN" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => (it > 0) ? 1 : (it < 0) ? -1 : 0);
}},
"ABS" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.abs(it));
}},
"SIN" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.sin(it));
}},
"COS" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.cos(it));
}},
"TAN" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.tan(it));
}},
"EXP" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.exp(it));
}},
"ASN" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.asin(it));
}},
"ACO" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.acos(it));
}},
"ATN" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.atan(it));
}},
"SQR" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.sqrt(it));
}},
"CBR" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.cbrt(it));
}},
"SINH" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.sinh(it));
}},
"COSH" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.cosh(it));
}},
"TANH" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.tanh(it));
}},
"LOG" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.log(it));
}},
"RESTORE" : {argc:0, f:function(lnum, stmtnum, args) {
    DATA_CURSOR = 0;
}},
"READ" : {argc:1, f:function(lnum, stmtnum, args) {
    if (args.length != 1) throw lang.syntaxfehler(lnum, args.length+lang.aG);
    let troValue = args[0].troValue;

    let rh = DATA_CONSTS[DATA_CURSOR++];
    if (rh === undefined) throw lang.outOfData(lnum);

    return bS.addAsBasicVar(lnum, troValue, rh);
}},
"DGET" : {argc:0, f:function(lnum, stmtnum, args) {
    let r = DATA_CONSTS[DATA_CURSOR++];
    if (r === undefined) throw lang.outOfData(lnum);
    return r;
}},
"OPTIONBASE" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => {
        if (lh != 0 && lh != 1) throw lang.syntaxfehler(line);
        INDEX_BASE = lh|0;
    });
}},
"DATA" : {f:function(lnum, stmtnum, args) {
    if (prescan) {
        args.forEach(it => DATA_CONSTS.push(resolve(it)));
    }
}},
/* Syopsis: MAP function, functor
 */
"MAP" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (fn, functor) => {
        if (!isRunnable(fn)) throw lang.badFunctionCallFormat(lnum, "first argument is not a function: got "+JStoBASICtype(fn));
        if (!isGenerator(functor) && !Array.isArray(functor)) throw lang.syntaxfehler(lnum, "not a mappable type: "+functor+((typeof functor == "object") ? Object.entries(functor) : ""));
        // generator?
        if (isGenerator(functor)) functor = genToArray(functor);

        return functor.map(it => bS.getDefunThunk(fn)(lnum, stmtnum, [it]));
    });
}},
/* Synopsis: FOLD function, init_value, functor
 * a function must accept two arguments, of which first argument will be an accumulator
 */
"FOLD" : {argc:3, f:function(lnum, stmtnum, args) {
    return threeArg(lnum, stmtnum, args, (fn, init, functor) => {
        if (!isRunnable(fn)) throw lang.badFunctionCallFormat(lnum, "first argument is not a function: got "+JStoBASICtype(fn));
        if (!isGenerator(functor) && !Array.isArray(functor)) throw lang.syntaxfehler(lnum, `not a mappable type '${Object.entries(args[2])}': `+functor+((typeof functor == "object") ? Object.entries(functor) : ""));
        // generator?
        if (isGenerator(functor)) functor = genToArray(functor);

        let akku = init;
        functor.forEach(it => {
            akku = bS.getDefunThunk(fn)(lnum, stmtnum, [akku, it]);
        });

        return akku;
    });
}},
/* Syopsis: FILTER function, functor
 */
"FILTER" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (fn, functor) => {
        if (!isRunnable(fn)) throw lang.badFunctionCallFormat(lnum, "first argument is not a function: got "+JStoBASICtype(fn));
        if (!isGenerator(functor) && !Array.isArray(functor)) throw lang.syntaxfehler(lnum, `not a mappable type '${Object.entries(args[1])}': `+functor+((typeof functor == "object") ? Object.entries(functor) : (typeof functor)));
        // generator?
        if (isGenerator(functor)) functor = genToArray(functor);

        return functor.filter(it => bS.getDefunThunk(fn)(lnum, stmtnum, [it]));
    });
}},
/* GOTO and GOSUB won't work but that's probably the best...? */
"DO" : {f:function(lnum, stmtnum, args) {
    return args[args.length - 1];
}},
"LABEL" : {f:function(lnum, stmtnum, args) {
    if (prescan) {
        let labelname = args[0].troValue;
        if (labelname === undefined) throw lang.syntaxfehler(lnum, "empty LABEL");
        gotoLabels[labelname] = lnum;
    }
}},
"ON" : {f:function(lnum, stmtnum, args) {
    //args: functionName (string), testvalue (SyntaxTreeReturnObj), arg0 (SyntaxTreeReturnObj), arg1 (SyntaxTreeReturnObj), ...
    if (args[2] === undefined) throw lang.syntaxfehler(lnum);

    let jmpFun = args.shift();
    let testvalue = resolve(args.shift())-INDEX_BASE;

    // args must be resolved lazily because jump label is not resolvable
    let jmpTarget = args[testvalue];

    if (jmpFun !== "GOTO" && jmpFun !== "GOSUB")
        throw lang.badFunctionCallFormat(lnum, `Not a jump statement: ${jmpFun}`)

    if (jmpTarget === undefined)
        return undefined;

    return bS.builtin[jmpFun].f(lnum, stmtnum, [jmpTarget]);
}},
"MIN" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (lh,rh) => (lh > rh) ? rh : lh);
}},
"MAX" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (lh,rh) => (lh < rh) ? rh : lh);
}},
"GETKEYSDOWN" : {argc:0, f:function(lnum, stmtnum, args) {
    let keys = [];
    sys.poke(-40, 255);
    for (let k = -41; k >= -48; k--) {
        keys.push(sys.peek(k));
    }
    return keys;
}},
"~<" : {argc:2, f:function(lnum, stmtnum, args) { // CURRY operator
    return twoArg(lnum, stmtnum, args, (fn, value) => {
        if (!isAST(fn)) throw lang.badFunctionCallFormat(lnum, "left-hand is not a function: got "+JStoBASICtype(fn));

        if (DBGON) {
            serial.println("[BASIC.BUILTIN.CURRY] currying this function tree...");
            serial.println(astToString(fn));
            serial.println("[BASIC.BUILTIN.CURRY] with this value: "+value);
            serial.println(Object.entries(value));
        }

        let curriedTree = curryDefun(fn, value);

        if (DBGON) {
            serial.println("[BASIC.BUILTIN.CURRY] Here's your curried tree:");
            serial.println(astToString(curriedTree));
        }

        return curriedTree;
    });
}},
"TYPEOF" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNul(lnum, stmtnum, args, bv => {
        if (bv === undefined) return "undefined";
        if (bv.bvType === undefined || !(bv instanceof BasicVar)) {
            let typestr = JStoBASICtype(bv);
            if (typestr == "monad")
                return bv.mType+"-"+typestr;
            else return typestr;
        }
        return bv.bvType;
    });
}},
"LEN" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArg(lnum, stmtnum, args, lh => {
        if (lh.length === undefined) throw lang.illegalType();
        return lh.length;
    });
}},
"HEAD" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArg(lnum, stmtnum, args, lh => {
        if (lh.length === undefined || lh.length < 1) throw lang.illegalType();
        return lh[0];
    });
}},
"TAIL" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArg(lnum, stmtnum, args, lh => {
        if (lh.length === undefined || lh.length < 1) throw lang.illegalType();
        return lh.slice(1, lh.length);
    });
}},
"INIT" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArg(lnum, stmtnum, args, lh => {
        if (lh.length === undefined || lh.length < 1) throw lang.illegalType();
        return lh.slice(0, lh.length - 1);
    });
}},
"LAST" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArg(lnum, stmtnum, args, lh => {
        if (lh.length === undefined || lh.length < 1) throw lang.illegalType();
        return lh[lh.length - 1];
    });
}},
"CLS" : {argc:0, f:function(lnum, stmtnum, args) {
    con.clear();
}},
"$" : {argc:2, f:function(lnum, stmtnum, args) {
    let fn = resolve(args[0]);
    let value = resolve(args[1]); // FIXME undefined must be allowed as we cannot distinguish between tree-with-value-of-undefined and just undefined
    
    if (DBGON) {
        serial.println("[BASIC.BUILTIN.APPLY] applying this function tree... "+fn);
        serial.println(astToString(fn));
        serial.println("[BASIC.BUILTIN.APPLY] with this value: "+value);
        if (value !== undefined)
            serial.println(Object.entries(value));
    }
    
    if (fn.mType == "funseq") {
        return getMonadEvalFun(fn)(lnum, stmtnum, [value]);
    }
    else {
        let valueTree = new BasicAST();
        valueTree.astLnum = lnum;
        valueTree.astType = JStoBASICtype(value);
        valueTree.astValue = value;
        
        
        let newTree = new BasicAST();
        newTree.astLnum = lnum;
        newTree.astValue = fn;
        newTree.astType = "usrdefun";
        newTree.astLeaves = [valueTree];

        if (DBGON) {
            serial.println("[BASIC.BUILTIN.APPLY] Here's your applied tree:");
            serial.println(astToString(newTree));
        }
        
        return bF._executeSyntaxTree(lnum, stmtnum, newTree, 0);
    }
}},
"REDUCE" : {noprod:1, argc:1, f:function(lnum, stmtnum, args) {
    return oneArg(lnum, stmtnum, args, bv => {
        if (isAST(bv)) {            
            if (DBGON) {
                serial.println("[BASIC.BUILTIN.REDUCE] reducing:");
                serial.println(astToString(bv));
                /*if (tree.astType == "usrdefun") {
                    serial.println("[BASIC.BUILTIN.REDUCE] usrdefun unpack:");
                    serial.println(astToString(tree.astValue));
                }*/
            }
            
            let reduced = bF._uncapAST(bv, it => {
                // TODO beta-eta reduction
                return it;
            });
            
            if (DBGON) {
                serial.println("[BASIC.BUILTIN.REDUCE] reduced: "+reduced);
                serial.println(astToString(reduced));
            }
            
            // re-wrap because tree-executor wants encapsulated function
            let newTree = new BasicAST();
            newTree.astLnum = lnum;
            newTree.astType = JStoBASICtype(reduced);
            newTree.astValue = reduced;
            
            return newTree;
        }
        else {
            return bv;
        }
    });
}},
/** type: m a -> (a -> m b) -> m b
 * @param m a monad
 * @param fnb a function that takes a monadic value from m and returns a new monad. IT'S ENTIRELY YOUR RESPONSIBILITY TO MAKE SURE THIS FUNCTION TO RETURN RIGHT KIND OF MONAD!
 * @return another monad
 */
">>=" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (ma, a_to_mb) => {
        if (!isMonad(ma)) throw lang.badFunctionCallFormat(lnum, "left-hand is not a monad: got "+JStoBASICtype(ma));
        if (!isRunnable(a_to_mb)) throw lang.badFunctionCallFormat(lnum, "right-hand is not a usrdefun: got "+JStoBASICtype(a_to_mb));
        
        if (DBGON) {
            serial.println("[BASIC.BIND] binder:");
            serial.println(monadToString(ma));
            serial.println("[BASIC.BIND] bindee:");
            serial.println(astToString(a_to_mb));
        }
        
        let a = ma.mVal;
        let mb = bS.getDefunThunk(a_to_mb)(lnum, stmtnum, [a]);
        
        if (!isMonad(mb)) throw lang.badFunctionCallFormat(lnum, "right-hand function did not return a monad");
                  
        if (DBGON) {
            serial.println("[BASIC.BIND] bound monad:");
            serial.println(monadToString(mb));
        }
        
        return mb;
    });
}},
/** type: m a -> m b -> m b
 * @param m a monad
 * @param fnb a function that returns a new monad. IT'S ENTIRELY YOUR RESPONSIBILITY TO MAKE SURE THIS FUNCTION TO RETURN RIGHT KIND OF MONAD!
 * @return another monad
 */
">>~" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (ma, mb) => {
        if (!isMonad(ma)) throw lang.badFunctionCallFormat(lnum, "left-hand is not a monad: got "+JStoBASICtype(ma));
        if (!isMonad(mb)) throw lang.badFunctionCallFormat(lnum, "right-hand is not a monad: got "+JStoBASICtype(mb));
        
        if (DBGON) {
            serial.println("[BASIC.BIND] binder:");
            serial.println(monadToString(ma));
            serial.println("[BASIC.BIND] bindee:");
            serial.println(monadToString(mb));
        }
        
        let a = ma.mVal;
        let b = mb.mVal;
        
        return mb;
    });
}},
/** type: (b -> c) -> (a -> b) -> (a -> c)
 * @param fa a function or a funseq-monad
 * @param fb a function or a funseq-monad
 * @return another monad
 */
"." : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (fa, fb) => {
        if (!isRunnable(fa)) throw lang.badFunctionCallFormat(lnum, "left-hand is not a function/funseq: got"+JStoBASICtype(fa));
        if (!isRunnable(fb)) throw lang.badFunctionCallFormat(lnum, "left-hand is not a function/funseq: got"+JStoBASICtype(fb));
                  
        let ma = (isAST(fa)) ? [fa] : fa.mVal;
        let mb = (isAST(fb)) ? [fb] : fb.mVal;
        
        let mc = mb.concat(ma);
        return new BasicFunSeq(mc);
    });
}},
"MLIST" : {noprod:1, argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNul(lnum, stmtnum, args, fn => {
        return new BasicListMonad([fn]);
    });
}},
"MRET" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArgNul(lnum, stmtnum, args, fn => {
        return new BasicMemoMonad(fn);
    });
}},
"MJOIN" : {argc:1, f:function(lnum, stmtnum, args) {
    return oneArg(lnum, stmtnum, args, m => {
        if (!isMonad(m)) throw lang.illegalType(lnum, m);
        return m.mVal;
    });
}},
"MEVAL" : {argc:1, f:function(lnum, stmtnum, args) {
    return varArg(lnum, stmtnum, args, rgs => {
        let m = rgs[0];
        let args = rgs.slice(1, rgs.length);
        return getMonadEvalFun(m)(lnum, stmtnum, args);
    });
}},
"GOTOYX" : {argc:2, f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (y, x) => {
        con.move(y + (1-INDEX_BASE),x + (1-INDEX_BASE));
    });
}},
"OPTIONDEBUG" : {f:function(lnum, stmtnum, args) {
    oneArgNum(lnum, stmtnum, args, (lh) => {
        if (lh != 0 && lh != 1) throw lang.syntaxfehler(line);
        DBGON = (1 == lh|0);
    });
}},
"OPTIONTRACE" : {f:function(lnum, stmtnum, args) {
    oneArgNum(lnum, stmtnum, args, (lh) => {
        if (lh != 0 && lh != 1) throw lang.syntaxfehler(line);
        TRACEON = (1 == lh|0);
    });
}},
"PRINTMONAD" : {debugonly:1, argc:1, f:function(lnum, stmtnum, args) {
    return oneArg(lnum, stmtnum, args, (it) => {
        println(monadToString(it));
    });
}}, 
"RESOLVE" : {debugonly:1, argc:1, f:function(lnum, stmtnum, args) {
    return oneArg(lnum, stmtnum, args, (it) => {
        if (isAST(it)) {
            println(lnum+" RESOLVE PRINTTREE")
            println(astToString(it));
            if (typeof it.astValue == "object") {
                if (isAST(it.astValue)) {
                    println(lnum+" RESOLVE PRINTTREE ASTVALUE PRINTTREE");
                    println(astToString(it.astValue));
                }
                else {
                    println(lnum+" RESOLVE PRINTTREE ASTVALUE");
                    println(it.astValue);
                }
            }
        }
        else
            println(it);
    });
}},
"RESOLVEVAR" : {debugonly:1, argc:1, f:function(lnum, stmtnum, args) {
    return oneArg(lnum, stmtnum, args, (it) => {
        let v = bS.vars[args[0].troValue];
        if (v === undefined) println("Undefined variable: "+args[0].troValue);
        else println(`type: ${v.bvType}, value: ${v.bvLiteral}`);
    });
}},
"UNRESOLVE" : {debugonly:1, argc:1, f:function(lnum, stmtnum, args) {
    println(args[0]);
}},
"UNRESOLVE0" : {debugonly:1, argc:1, f:function(lnum, stmtnum, args) {
    println(Object.entries(args[0]));
}}
};
Object.freeze(bS.builtin);
let bF = {}; // BASIC functions
bF._1os = {"!":1,"~":1,"#":1,"<":1,"=":1,">":1,"*":1,"+":1,"-":1,"/":1,"^":1,":":1,"$":1,".":1};
//bF._2os = {"<":1,"=":1,">":1,"~":1,"-":1,"$":1,"*":1,"!":1,"#":1};
//bF._3os = {"<":1,"=":1,">":1,"~":1,"-":1,"$":1,"*":1}
bF._uos = {"+":1,"-":1,"NOT":1,"BNOT":1};
bF._isNum = function(code) {
    return (code >= 0x30 && code <= 0x39) || code == 0x5F;
};
bF._isNum2 = function(code) {
    return (code >= 0x30 && code <= 0x39) || code == 0x5F || (code >= 0x41 && code <= 0x46) || (code >= 0x61 && code <= 0x66);
};
bF._isNumSep = function(code) {
    return code == 0x2E || code == 0x42 || code == 0x58 || code == 0x62 || code == 0x78;
};
bF._is1o = function(code) {
    return bF._1os[String.fromCharCode(code)]
};
/*bF._is2o = function(code) {
    return bF._2os[String.fromCharCode(code)]
};
bF._is3o = function(code) {
    return bF._3os[String.fromCharCode(code)]
};*/
bF._isUnary = function(code) {
    return bF._uos[String.fromCharCode(code)]
}
bF._isParenOpen = function(code) {
    return (code == 0x28 || code == 0x5B) || (code == '(' || code == '[');
};
bF._isParenClose = function(code) {
    return (code == 0x29 || code == 0x5D) || (code == ')' || code == ']');
};
bF._isMatchingParen = function(open, close) {
    return (open == '(' && close == ')' || open == '[' && close == ']');
};
bF._isParen = function(code) {
    return bF._isParenOpen(code) || bF._isParenClose(code);
};
bF._isSep = function(code) {
    return code == 0x2C || code == 0x3B;
};
// define operator precedence here...
// NOTE: do NOT put falsy value (e.g. 0) here!!
bF._opPrc = {
    // function call in itself has highest precedence
    "^":1,
    "*":2,"/":2,"\\":2,
    "MOD":3,
    "+":4,"-":4,
    "NOT":5,"BNOT":5,
    "<<":6,">>":6,
    "<":7,">":7,"<=":7,"=<":7,">=":7,"=>":7,
    "==":8,"<>":8,"><":8,
    "MIN":10,"MAX":10,
    "BAND":20,
    "BXOR":21,
    "BOR":22,
    "AND":30,
    "OR":31,
    "TO":40,
    "STEP":41,
    "!":50,"~":51, // array CONS and PUSH
    "#":52, // array concat
    ".": 60, // compo operator
    "$": 60, // apply operator
    "~<": 61, // curry operator
    "~>": 100, // closure operator
    ">>~": 100, // monad sequnce operator
    ">>=": 100, // monad bind operator
    "=":999,"IN":999
}; // when to ops have same index of prc but different in associativity, right associative op gets higher priority (at least for the current parser implementation)
bF._opRh = {"^":1,"=":1,"!":1,"IN":1,"~>":1,"$":1,".":1,">>=":1,">>~":1,">!>":1}; // ~< and ~> cannot have same associativity
// these names appear on executeSyntaxTree as "exceptional terms" on parsing (regular function calls are not "exceptional terms")
bF._tokenise = function(lnum, cmd) {
    var _debugprintStateTransition = false;
    var k;
    var tokens = [];
    var states = [];
    var sb = "";
    var mode = "lit"; // lit, qot, paren, sep, op, num; operator2, numbersep, number2, limbo, escape, quote_end

    // NOTE: malformed numbers (e.g. "_b3", "_", "__") must be re-marked as literal or syntax error in the second pass

    if (_debugprintStateTransition) println("@@ TOKENISE @@");
    if (_debugprintStateTransition) println("Ln "+lnum+" cmd "+cmd);

    // TOKENISE
    for (k = 0; k < cmd.length; k++) {
        var char = cmd[k];
        var charCode = cmd.charCodeAt(k);

        if (_debugprintStateTransition) print("Char: "+char+"("+charCode+"), state: "+mode);

        if ("lit" == mode) {
            if (0x22 == charCode) { // "
                tokens.push(sb); sb = ""; states.push(mode);
                mode = "qot";
            }
            else if (bF._isParen(charCode)) {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "paren";
            }
            else if (" " == char) {
                tokens.push(sb); sb = ""; states.push(mode);
                mode = "limbo";
            }
            else if (bF._isSep(charCode)) {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "sep";
            }
            /*else if (bF._isNum(charCode)) {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "num";
            }*/
            else if (bF._is1o(charCode)) {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "op";
            }
            else {
                sb += char;
            }
        }
        else if ("num" == mode) {
            if (bF._isNum(charCode)) {
                sb += char;
            }
            else if (bF._isNumSep(charCode)) {
                sb += char;
                mode = "nsep";
            }
            else if (0x22 == charCode) {
                tokens.push(sb); sb = ""; states.push(mode);
                mode = "qot";
            }
            else if (" " == char) {
                tokens.push(sb); sb = ""; states.push(mode);
                mode = "limbo";
            }
            else if (bF._isParen(charCode)) {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "paren"
            }
            else if (bF._isSep(charCode)) {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "sep";
            }
            else if (bF._is1o(charCode)) {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "op";
            }
            else {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "lit";
            }
        }
        else if ("nsep" == mode) {
            if (bF._isNum2(charCode)) {
                sb += char;
                mode = "n2";
            }
            else {
                throw lang.syntaxfehler(lnum, lang.badNumberFormat);
            }
        }
        else if ("n2" == mode) {
            if (bF._isNum2(charCode)) {
                sb += char;
            }
            else if (0x22 == charCode) {
                tokens.push(sb); sb = ""; states.push("num");
                mode = "qot";
            }
            else if (" " == char) {
                tokens.push(sb); sb = ""; states.push("num");
                mode = "limbo";
            }
            else if (bF._isParen(charCode)) {
                tokens.push(sb); sb = "" + char; states.push("num");
                mode = "paren"
            }
            else if (bF._isSep(charCode)) {
                tokens.push(sb); sb = "" + char; states.push("num");
                mode = "sep";
            }
            else if (bF._is1o(charCode)) {
                tokens.push(sb); sb = "" + char; states.push("num");
                mode = "op";
            }
            else {
                tokens.push(sb); sb = "" + char; states.push("num");
                mode = "lit";
            }
        }
        else if ("op" == mode) {
            if (bF._is1o(charCode)) {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "op";
            }
            else if (bF._isUnary(charCode)) {
                tokens.push(sb); sb = "" + char; states.push(mode);
            }
            else if (bF._isNum(charCode)) {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "num";
            }
            else if (0x22 == charCode) {
                tokens.push(sb); sb = ""; states.push(mode);
                mode = "qot";
            }
            else if (" " == char) {
                tokens.push(sb); sb = ""; states.push(mode);
                mode = "limbo";
            }
            else if (bF._isParen(charCode)) {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "paren"
            }
            else if (bF._isSep(charCode)) {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "sep";
            }
            else {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "lit";
            }
        }
        else if ("qot" == mode) {
            if (0x22 == charCode) {
                tokens.push(sb); sb = ""; states.push(mode);
                mode = "quote_end";
            }
            /*else if (charCode == 0x5C) { // reverse solidus
                tokens.push(sb); sb = "";
                mode = "escape";
            }*/
            else {
                sb += char;
            }
        }
        /*else if ("escape" == mode) {
            if (0x5C == charCode) // reverse solidus
                sb += String.fromCharCode(0x5C);
            else if ("n" == char)
                sb += String.fromCharCode(0x0A);
            else if ("t" == char)
                sb += String.fromCharCode(0x09);
            else if (0x22 == charCode) // "
                sb += String.fromCharCode(0x22);
            else if (0x27 == charCode)
                sb += String.fromCharCode(0x27);
            else if ("e" == char)
                sb += String.fromCharCode(0x1B);
            else if ("a" == char)
                sb += String.fromCharCode(0x07);
            else if ("b" == char)
                sb += String.fromCharCode(0x08);
            mode = "qot"; // ESCAPE is only legal when used inside of quote
        }*/
        else if ("quote_end" == mode) {
            if (" " == char) {
                sb = "";
                mode = "limbo";
            }
            else if (0x22 == charCode) {
                sb = "" + char;
                mode = "qot";
            }
            else if (bF._isParen(charCode)) {
                sb = "" + char;
                mode = "paren";
            }
            else if (bF._isSep(charCode)) {
                sb = "" + char;
                mode = "sep";
            }
            else if (bF._isNum(charCode)) {
                sb = "" + char;
                mode = "num";
            }
            else if (bF._is1o(charCode)) {
                sb = "" + char;
                mode = "op"
            }
            else {
                sb = "" + char;
                mode = "lit";
            }
        }
        else if ("limbo" == mode) {
            if (char == " ") {
                /* do nothing */
            }
            else if (0x22 == charCode) {
                mode = "qot"
            }
            else if (bF._isParen(charCode)) {
                sb = "" + char;
                mode = "paren";
            }
            else if (bF._isSep(charCode)) {
                sb = "" + char;
                mode = "sep";
            }
            else if (bF._isNum(charCode)) {
                sb = "" + char;
                mode = "num";
            }
            else if (bF._is1o(charCode)) {
                sb = "" + char;
                mode = "op"
            }
            else {
                sb = "" + char;
                mode = "lit";
            }
        }
        else if ("paren" == mode) {
            if (char == " ") {
                tokens.push(sb); sb = ""; states.push(mode);
                mode = "limbo";
            }
            else if (0x22 == charCode) {
                tokens.push(sb); sb = ""; states.push(mode);
                mode = "qot"
            }
            else if (bF._isParen(charCode)) {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "paren";
            }
            else if (bF._isSep(charCode)) {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "sep";
            }
            else if (bF._isNum(charCode)) {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "num";
            }
            else if (bF._is1o(charCode)) {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "op"
            }
            else {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "lit";
            }
        }
        else if ("sep" == mode) {
            if (char == " ") {
                tokens.push(sb); sb = ""; states.push(mode);
                mode = "limbo";
            }
            else if (0x22 == charCode) {
                tokens.push(sb); sb = ""; states.push(mode);
                mode = "qot"
            }
            else if (bF._isParen(charCode)) {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "paren";
            }
            else if (bF._isSep(charCode)) {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "sep";
            }
            else if (bF._isNum(charCode)) {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "num";
            }
            else if (bF._is1o(charCode)) {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "op"
            }
            else {
                tokens.push(sb); sb = "" + char; states.push(mode);
                mode = "lit";
            }
        }
        else {
            throw Error("Unknown parser state: " + mode);
        }

        if (_debugprintStateTransition) println("->"+mode);
    }

    if (sb.length > 0) {
        tokens.push(sb); states.push(mode);
    }

    // filter off initial empty token if the statement does NOT start with literal (e.g. "-3+5")
    if (tokens[0].length == 0) {
        tokens = tokens.slice(1, tokens.length);
        states = states.slice(1, states.length);
    }
    // clean up operator2 and number2
    for (k = 0; k < states.length; k++) {
        if (states[k] == "o2" || states[k] == "o3") states[k] = "op";
        else if (states[k] == "n2" || states[k] == "nsep") states[k] = "num";
    }

    if (tokens.length != states.length) {
        throw new InternalError("size of tokens and states does not match (line: "+lnum+")\n"+
        tokens+"\n"+states);
    }

    return { "tokens": tokens, "states": states };
};
bF._parserElaboration = function(lnum, ltokens, lstates) {
    let _debugprintElaboration = false;
    if (_debugprintElaboration) println("@@ ELABORATION @@");
    
    let tokens = cloneObject(ltokens);
    let states = cloneObject(lstates);
    
    let k = 0;

    // NOTE: malformed numbers (e.g. "_b3", "_", "__") must be re-marked as literal or syntax error
    
    while (k < states.length) { // using while loop because array size will change during the execution
        // turn errenously checked as number back into a literal
        if (states[k] == "num" && !reNumber.test(tokens[k]))
            states[k] = "lit";
        // turn back into an op if operator is errenously checked as a literal
        else if (states[k] == "lit" && bF._opPrc[tokens[k].toUpperCase()] !== undefined)
            states[k] = "op";
        // turn TRUE and FALSE into boolean
        else if ((tokens[k].toUpperCase() == "TRUE" || tokens[k].toUpperCase() == "FALSE") && states[k] != "qot")
            states[k] = "bool";
        
        // decimalise hex/bin numbers (because Nashorn does not support binary literal)
        if (states[k] == "num") {
            if (tokens[k].toUpperCase().startsWith("0B")) {
                tokens[k] = parseInt(tokens[k].substring(2, tokens[k].length), 2) + "";
            }
        }

        k += 1;
    }
        
    k = 0; let l = states.length;
    while (k < l) {
        let lookahead012 = tokens[k]+tokens[k+1]+tokens[k+2];
        let lookahead01 = tokens[k]+tokens[k+1]
        
        // turn three consecutive ops into a trigraph
        if (k < states.length - 3 && states[k] == "op" && states[k+1] == "op" && states[k+2] == "op" && bF._opPrc[lookahead012]) {
            serial.println(`[ParserElaboration] Line ${lnum}: Trigraph (${lookahead012}) found starting from the ${lang.ord(k+1)} token of [${tokens}]`);
            
            tokens[k] = lookahead012
            
            // remove two future elements by splicing them
            let oldtkn = cloneObject(tokens);
            let oldsts = cloneObject(states);
            tokens = oldtkn.slice(0, k+1).concat(oldtkn.slice(k+3, oldtkn.length));
            states = oldsts.slice(0, k+1).concat(oldsts.slice(k+3, oldsts.length));
            l -= 2;
        }
        // turn two consecutive ops into a digraph
        else if (k < states.length - 2 && states[k] == "op" && states[k+1] == "op" && bF._opPrc[lookahead01]) {
            serial.println(`[ParserElaboration] Line ${lnum}: Digraph (${lookahead01}) found starting from the ${lang.ord(k+1)} token of [${tokens}]`);
            
            tokens[k] = lookahead01;
            
            // remove two future elements by splicing them
            let oldtkn = cloneObject(tokens);
            let oldsts = cloneObject(states);
            tokens = oldtkn.slice(0, k+1).concat(oldtkn.slice(k+2, oldtkn.length));
            states = oldsts.slice(0, k+1).concat(oldsts.slice(k+2, oldsts.length));
            l -= 1;
        }
        // turn (:) into a seq
        else if (tokens[k] == ":" && states[k] == "op")
            states[k] = "seq";

        k += 1;
    }
    
    return {"tokens":tokens, "states":states};
};
/**
 * Destructively transforms an AST (won't unpack capsulated trees by default)
 * 
 * To NOT modify the tree, make sure you're not modifying any properties of the object */
bF._recurseApplyAST = function(tree, action) {
    if (!isAST(tree)) throw new InternalError(`tree is not a AST (${tree})`);
    
    if (tree.astLeaves !== undefined && tree.astLeaves[0] === undefined) {
        /*if (DBGON) {
            serial.println(`RECURSE astleaf`);
            serial.println(astToString(tree));
        }*/
        
        return action(tree) || tree;
    }
    else {
        let newLeaves = tree.astLeaves.map(it => bF._recurseApplyAST(it, action))
        
        /*if (DBGON) {
            serial.println(`RECURSE ast`);
            serial.println(astToString(tree));
        }*/
        
        let newTree = action(tree);
        
        if (newTree !== undefined) {
            tree.astLnum = newTree.astLnum;
            tree.astValue = newTree.astValue;
            tree.astSeps = newTree.astSeps;
            tree.astType = newTree.astType;
            // weave astLeaves
            for (let k = 0; k < tree.astLeaves.length; k++) {
                if (newLeaves[k] !== undefined) tree.astLeaves[k] = newLeaves[k];
            }
        }
    }
}
/**
 * Returns a copy of BasicAST where its 'capsulated' trees are fully uncapsulated.
 */
bF._uncapAST = function(tree, action) {
    let expr = cloneObject(tree);
    bF._recurseApplyAST(expr, it => {
        if (isAST(it.astValue)) {
            let capTree = bF._uncapAST(it.astValue, action);
            it.astLnum = capTree.astLnum;
            it.astValue = capTree.astValue;
            it.astSeps = capTree.astSeps;
            it.astType = capTree.astType;
            it.astLeaves = capTree.astLeaves;
        }
        
        return action(it);
    });
    action(expr);
    return expr;
}
/** EBNF notation:
(* quick reference to EBNF *)
(* { word } = word is repeated 0 or more times *)
(* [ word ] = word is optional (repeated 0 or 1 times) *)

line =
      linenumber , stmt , {":" , stmt}
    | linenumber , "REM" , ? basically anything ? ;
linenumber = digits ;

stmt =
      "REM" , ? anything ?
    | "IF" , expr_sans_asgn , "THEN" , stmt , ["ELSE" , stmt]
    | "DEFUN" , [ident] , "(" , [ident , {" , " , ident}] , ")" , "=" , expr
    | "ON" , expr_sans_asgn , ("GOTO" | "GOSUB") , expr_sans_asgn , {"," , expr_sans_asgn}
    | "(" , stmt , ")"
    | expr ; (* if the statement is 'lit' and contains only one word, treat it as function_call
                e.g. NEXT for FOR loop *)
    
expr = (* this basically blocks some funny attemps such as using DEFUN as anon function
          because everything is global in BASIC *)
      lit
    | "(" , expr , ")"
    | ident_tuple
    | "IF" , expr_sans_asgn , "THEN" , expr , ["ELSE" , expr]
    | kywd , expr - "(" (* also deals with FOR statement *)
    (* at this point, if OP is found in paren-level 0, skip function_call *)
    | function_call
    | expr , op , expr
    | op_uni , expr ;
    
expr_sans_asgn = ? identical to expr except errors out whenever "=" is found ? ;
        
ident_tuple = "[" , ident , ["," , ident] , "]" ;
    
function_call =
      ident , "(" , [expr , {argsep , expr} , [argsep]] , ")"
    | ident , expr , {argsep , expr} , [argsep] ;
kywd = ? words that exists on the list of predefined function that are not operators ? ;
    
(* don't bother looking at these, because you already know the stuff *)    
    
argsep = "," | ";" ;
ident = alph , [digits] ; (* variable and function names *)
lit = alph , [digits] | num | string ; (* ident + numbers and string literals *)
op = "^" | "*" | "/" | "MOD" | "+" | "-" | "<<" | ">>" | "<" | ">" | "<="
    | "=<" | ">=" | "=>" | "==" | "<>" | "><" | "BAND" | "BXOR" | "BOR"
    | "AND" | "OR" | "TO" | "STEP" | "!" | "~" | "#" | "=" ;
op_uni = "-" | "+" ;

alph = letter | letter , alph ;
digits = digit | digit , digits ;
hexdigits = hexdigit | hexdigit , hexdigits ;
bindigits = bindigit | bindigit , bindigits ;
num = digits | digits , "." , [digits] | "." , digits
    | ("0x"|"0X") , hexdigits 
    | ("0b"|"0B") , bindigits ; (* sorry, no e-notation! *)
visible = ? ASCII 0x20 to 0x7E ? ;
string = '"' , (visible | visible , stringlit) , '"' ;

letter = "A" | "B" | "C" | "D" | "E" | "F" | "G" | "H" | "I" | "J" | "K" | "L" | "M" | "N"
    | "O" | "P" | "Q" | "R" | "S" | "T" | "U" | "V" | "W" | "X" | "Y" | "Z" | "a" | "b"
    | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | "k" | "l" | "m" | "n" | "o" | "p"
    | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x" | "y" | "z" | "_" ;
digit = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ;
hexdigit = "A" | "B" | "C" | "D" | "E" | "F" | "a" | "b" | "c" | "d" | "e" | "f" | "0" | "1"
    | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ;
bindigit = "0" | "1" ;

(* all possible token states: lit num op bool qot paren sep *)
(* below are schematic of trees generated after parsing the statements *)

IF (type: function, value: IF)
1. cond
2. true
[3. false]

FOR (type: function, value: FOR)
1. expr (normally (=) but not necessarily)

DEFUN (type: function, value: DEFUN)
1. funcname (type: lit)
    1. arg0 (type: lit)
    [2. arg1]
    [3. argN...]
2. stmt

ON (type: function, value: ON)
1. testvalue
2. functionname (type: lit)
3. arg0
[4. arg1]
[5. argN...]

FUNCTION_CALL (type: function, value: PRINT or something)
1. arg0
2. arg1
[3. argN...]

LAMBDA (type: op, value: "~>")
1. undefined (type: closure_args, value: undefined)
    1. arg0 (type: lit)
    [2. arg1]
    [3. argN...]
2. stmt
 */
// @returns BasicAST
bF._EquationIllegalTokens = ["IF","THEN","ELSE","DEFUN","ON"];
bF.isSemanticLiteral = function(token, state) {
    return undefined == token || "]" == token || ")" == token ||
            "qot" == state || "num" == state || "bool" == state || "lit" == state;
}
bF.parserDoDebugPrint = (!PROD) && true;
bF.parserPrintdbg = any => { if (bF.parserDoDebugPrint) serial.println(any) };
bF.parserPrintdbg2 = function(icon, lnum, tokens, states, recDepth) {
    if (bF.parserDoDebugPrint) {
        let treeHead = "|  ".repeat(recDepth);
        bF.parserPrintdbg(`${icon}${lnum} ${treeHead}${tokens.join(' ')}`);
        bF.parserPrintdbg(`${icon}${lnum} ${treeHead}${states.join(' ')}`);
    }
}
bF.parserPrintdbgline = function(icon, msg, lnum, recDepth) {
    if (bF.parserDoDebugPrint) {
        let treeHead = "|  ".repeat(recDepth);
        bF.parserPrintdbg(`${icon}${lnum} ${treeHead}${msg}`);
    }
}

// ## USAGE OF lambdaBoundVars IN PARSEMODE STARTS HERE ##

/**
 * @return ARRAY of BasicAST
 */
bF._parseTokens = function(lnum, tokens, states) {
    if (tokens.length !== states.length) throw Error("unmatched tokens and states length");
    
    bF.parserPrintdbg2('Line ', lnum, tokens, states, 0);

    if (tokens.length !== states.length) throw lang.syntaxfehler(lnum);
    if (tokens[0].toUpperCase() == "REM" && states[0] != "qot") return;

    /*************************************************************************/

    let parenDepth = 0;
    let parenStart = -1;
    let parenEnd = -1;
    let seps = [];
    
    // scan for parens and (:)s
    for (let k = 0; k < tokens.length; k++) {
        // increase paren depth and mark paren start position
        if (tokens[k] == "(" && states[k] != "qot") {
            parenDepth += 1;
            if (parenStart == -1 && parenDepth == 1) parenStart = k;
        }
        // decrease paren depth
        else if (tokens[k] == ")" && states[k] != "qot") {
            if (parenEnd == -1 && parenDepth == 1) parenEnd = k;
            parenDepth -= 1;
        }

        if (parenDepth == 0 && tokens[k] == ":" && states[k] == "seq")
            seps.push(k);
    }
    
    let startPos = [0].concat(seps.map(k => k+1));
    let stmtPos = startPos.map((s,i) => {return{start:s, end:(seps[i] || tokens.length)}}); // use end of token position as separator position
    
    return stmtPos.map((x,i) => {
        if (stmtPos.length > 1)
            bF.parserPrintdbgline('Line ', 'Statement #'+(i+1), lnum, 0);
        
        // check for empty tokens
        if (x.end - x.start <= 0) throw new ParserError("Malformed Line");
        
        let tree = bF._parseStmt(lnum,
            tokens.slice(x.start, x.end),
            states.slice(x.start, x.end),
            1
        );

        bF.parserPrintdbgline('Tree in ', '\n'+astToString(tree), lnum, 0);

        return tree;
    });
}
/** Parses following EBNF rule:
stmt =
      "IF" , expr_sans_asgn , "THEN" , stmt , ["ELSE" , stmt]
    | "DEFUN" , [ident] , "(" , [ident , {" , " , ident}] , ")" , "=" , expr
    | "ON" , expr_sans_asgn , ident , expr_sans_asgn , {"," , expr_sans_asgn}
    | "(" , stmt , ")"
    | expr ; (* if the statement is 'lit' and contains only one word, treat it as function_call e.g. NEXT for FOR loop *)
 * @return: BasicAST
 */
bF._parseStmt = function(lnum, tokens, states, recDepth) {
    bF.parserPrintdbg2('$', lnum, tokens, states, recDepth);

    /*************************************************************************/

    // case for: single word (e.g. NEXT for FOR loop)
    if (tokens.length == 1 && states.length == 1) {
        bF.parserPrintdbgline('$', "Single Word Function Call", lnum, recDepth);
        return bF._parseLit(lnum, tokens, states, recDepth + 1, true);
    }

    /*************************************************************************/

    let headTkn = tokens[0].toUpperCase();
    let headSta = states[0];

    let treeHead = new BasicAST();
    treeHead.astLnum = lnum;

    /*************************************************************************/

    // case for: "REM" , ? anything ?
    if (headTkn == "REM" && headSta != "qot") return;

    /*************************************************************************/

    let parenDepth = 0;
    let parenStart = -1;
    let parenEnd = -1;
    let onGoPos = -1;
    let sepsZero = [];
    let sepsOne = [];

    // scan for parens that will be used for several rules
    // also find nearest THEN and ELSE but also take parens into account
    for (let k = 0; k < tokens.length; k++) {
        // increase paren depth and mark paren start position
        if (tokens[k] == "(" && states[k] != "qot") {
            parenDepth += 1;
            if (parenStart == -1 && parenDepth == 1) parenStart = k;
        }
        // decrease paren depth
        else if (tokens[k] == ")" && states[k] != "qot") {
            if (parenEnd == -1 && parenDepth == 1) parenEnd = k;
            parenDepth -= 1;
        }

        if (parenDepth == 0 && states[k] == "sep")
            sepsZero.push(k);
        if (parenDepth == 1 && states[k] == "sep")
            sepsOne.push(k);

        if (parenDepth == 0) {
            let tok = tokens[k].toUpperCase();
            if (-1 == onGoPos && ("GOTO" == tok || "GOSUB" == tok) && "lit" == states[k])
                onGoPos = k;
        }
    }

    // unmatched brackets, duh!
    if (parenDepth != 0) throw lang.syntaxfehler(lnum, lang.unmatchedBrackets);

    /*************************************************************************/

    // ## case for:
    //      "IF" , expr_sans_asgn , "THEN" , stmt , ["ELSE" , stmt]
    try {
        bF.parserPrintdbgline('$', "Trying IF Statement...", lnum, recDepth);
        return bF._parseIfMode(lnum, tokens, states, recDepth + 1, false);
    }
    // if ParserError is raised, continue to apply other rules
    catch (e) {
        if (!(e instanceof ParserError)) throw e;
        bF.parserPrintdbgline('$', 'It was NOT!', lnum, recDepth);
    }

    /*************************************************************************/

    // ## case for:
    //    | "DEFUN" , [ident] , "(" , [ident , {" , " , ident}] , ")" , "=" , expr
    if ("DEFUN" == headTkn && "lit" == headSta &&
        parenStart == 2 && tokens[parenEnd + 1] == "=" && states[parenEnd + 1] == "op"
    ) {
        bF.parserPrintdbgline('$', 'DEFUN Stmt', lnum, recDepth);

        treeHead.astValue = "DEFUN";
        treeHead.astType = "function";

        // parse function name
        if (tokens[1] == "(") {
            // anonymous function
            treeHead.astLeaves[0] = new BasicAST();
            treeHead.astLeaves[0].astLnum = lnum;
            treeHead.astLeaves[0].astType = "lit";
        }
        else {
            bF.parserPrintdbgline('$', 'DEFUN Stmt Function Name:', lnum, recDepth);
            treeHead.astLeaves[0] = bF._parseIdent(lnum, [tokens[1]], [states[1]], recDepth + 1);
        }

        // parse function arguments
        bF.parserPrintdbgline('$', 'DEFUN Stmt Function Arguments -- ', lnum, recDepth);
        let defunArgDeclSeps = sepsOne.filter((i) => i < parenEnd + 1).map(i => i-1).concat([parenEnd - 1]);
        bF.parserPrintdbgline('$', 'DEFUN Stmt Function Arguments comma position: '+defunArgDeclSeps, lnum, recDepth);

        treeHead.astLeaves[0].astLeaves = defunArgDeclSeps.map(i=>bF._parseIdent(lnum, [tokens[i]], [states[i]], recDepth + 1));

        // parse function body
        let parseFunction = (DEFUNS_BUILD_DEFUNS) ? bF._parseStmt : bF._parseExpr;
        treeHead.astLeaves[1] = parseFunction(lnum,
            tokens.slice(parenEnd + 2, tokens.length),
            states.slice(parenEnd + 2, states.length),
            recDepth + 1
        );

        return treeHead;
    }

    /*************************************************************************/

    // ## case for:
    //    | "ON" , if_equation , ident , if_equation , {"," , if_equation}
    if ("ON" == headTkn && "lit" == headSta) {
        bF.parserPrintdbgline('$', 'ON Stmt', lnum, recDepth);

        if (onGoPos == -1) throw ParserError("Malformed ON Statement");

        treeHead.astValue = "ON";
        treeHead.astType = "function";

        // parse testvalue
        let testvalue = bF._parseExpr(lnum,
            tokens.slice(1, onGoPos),
            states.slice(1, onGoPos),
            recDepth + 1,
            true
        );

        // parse functionname
        let functionname = bF._parseExpr(lnum,
            [tokens[onGoPos]],
            [states[onGoPos]],
            recDepth + 1,
            true
        );

        // parse arguments
        // get list of comma but filter ones appear before GOTO/GOSUB
        let onArgSeps = sepsZero.filter(i => (i > onGoPos));
        let onArgStartPos = [onGoPos + 1].concat(onArgSeps.map(k => k + 1));
        let onArgPos = onArgStartPos.map((s,i) => {return{start:s, end: (onArgSeps[i] || tokens.length)}}); // use end of token position as separator position

        // recursively parse expressions
        treeHead.astLeaves = [testvalue, functionname].concat(onArgPos.map((x,i) => {
            bF.parserPrintdbgline('$', 'ON GOTO/GOSUB Arguments #'+(i+1), lnum, recDepth);

            // check for empty tokens
            if (x.end - x.start <= 0) throw new ParserError("Malformed ON arguments");

            return bF._parseExpr(lnum,
                tokens.slice(x.start, x.end),
                states.slice(x.start, x.end),
                recDepth + 1,
                true
            );
        }));

        return treeHead;
    }

    /*************************************************************************/

    // ## case for:
    //    | "(" , stmt , ")"
    if (parenStart == 0 && parenEnd == tokens.length - 1) {
        bF.parserPrintdbgline('$', '( Stmt )', lnum, recDepth);
        return bF._parseStmt(lnum,
            tokens.slice(parenStart + 1, parenEnd),
            states.slice(parenStart + 1, parenEnd),
            recDepth + 1
        );
    }

    /*************************************************************************/

    // ## case for:
    //    | expr ;
    try {
        bF.parserPrintdbgline('$', 'Trying Expression Call...', lnum, recDepth);
        return bF._parseExpr(lnum, tokens, states, recDepth + 1);
    }
    catch (e) {
        bF.parserPrintdbgline('$', 'Error!', lnum, recDepth);
        throw new ParserError("Statement cannot be parsed in "+lnum+": "+e.stack);
    }

    /*************************************************************************/

    throw new ParserError("Statement cannot be parsed in "+lnum);
} // END of STMT
/** Parses following EBNF rule:
expr = (* this basically blocks some funny attemps such as using DEFUN as anon function because everything is global in BASIC *)
      lit
    | "(" , expr , ")"
    | tuple
    | "IF" , expr_sans_asgn , "THEN" , expr , ["ELSE" , expr]
    | kywd , expr - "(" (* also deals with FOR statement *)
    (* at this point, if OP is found in paren-level 0, skip function_call *)
    | function_call
    | expr , op , expr
    | op_uni , expr ;

 * @return: BasicAST
 */
bF._parseExpr = function(lnum, tokens, states, recDepth, ifMode) {
    bF.parserPrintdbg2('e', lnum, tokens, states, recDepth);

    /*************************************************************************/

    // ## special case for virtual dummy element (e.g. phantom element on "PRINT SPC(20);")
    if (tokens[0] === undefined && states[0] === undefined) {
        let treeHead = new BasicAST();
        treeHead.astLnum = lnum;
        treeHead.astValue = undefined;
        treeHead.astType = "null";

        return treeHead;
    }

    /*************************************************************************/

    let headTkn = tokens[0].toUpperCase();
    let headSta = states[0];

    /*************************************************************************/

    // ## case for:
    //    lit
    if (!bF._EquationIllegalTokens.includes(headTkn) && tokens.length == 1) {
        bF.parserPrintdbgline('e', 'Literal Call', lnum, recDepth);
        return bF._parseLit(lnum, tokens, states, recDepth + 1);
    }

    /*************************************************************************/

    // scan for operators with highest precedence, use rightmost one if multiple were found
    let topmostOp;
    let topmostOpPrc = 0;
    let operatorPos = -1;

    // find and mark position of parentheses
    // properly deal with the nested function calls
    let parenDepth = 0;
    let parenStart = -1;
    let parenEnd = -1;

    // Scan for unmatched parens and mark off the right operator we must deal with
    // every function_call need to re-scan because it is recursively called
    for (let k = 0; k < tokens.length; k++) {
        // increase paren depth and mark paren start position
        if (tokens[k] == "(" && states[k] != "qot") {
            parenDepth += 1;
            if (parenStart == -1 && parenDepth == 1) parenStart = k;
        }
        // decrease paren depth
        else if (tokens[k] == ")" && states[k] != "qot") {
            if (parenEnd == -1 && parenDepth == 1) parenEnd = k;
            parenDepth -= 1;
        }

        // determine the right operator to deal with
        if (parenDepth == 0) {
            if (states[k] == "op" && bF.isSemanticLiteral(tokens[k-1], states[k-1]) &&
                    ((bF._opPrc[tokens[k].toUpperCase()] > topmostOpPrc) ||
                        (!bF._opRh[tokens[k].toUpperCase()] && bF._opPrc[tokens[k].toUpperCase()] == topmostOpPrc))
            ) {
                topmostOp = tokens[k].toUpperCase();
                topmostOpPrc = bF._opPrc[tokens[k].toUpperCase()];
                operatorPos = k;
            }
        }
    }

    // unmatched brackets, duh!
    if (parenDepth != 0) throw lang.syntaxfehler(lnum, lang.unmatchedBrackets);

    /*************************************************************************/
    
    // ## case for:
    //    | ident_tuple
    try {
        bF.parserPrintdbgline('e', "Trying Tuple...", lnum, recDepth);
        return bF._parseTuple(lnum, tokens, states, recDepth + 1, false);
    }
    // if ParserError is raised, continue to apply other rules
    catch (e) {
        if (!(e instanceof ParserError)) throw e;
        bF.parserPrintdbgline('e', 'It was NOT!', lnum, recDepth);
    }
    
    /*************************************************************************/

    // ## case for:
    //    | "(" , expr , ")"
    if (parenStart == 0 && parenEnd == tokens.length - 1) {
        bF.parserPrintdbgline('e', '( Expr )', lnum, recDepth);

        return bF._parseExpr(lnum,
            tokens.slice(parenStart + 1, parenEnd),
            states.slice(parenStart + 1, parenEnd),
            recDepth + 1
        );
    }

    /*************************************************************************/

    // ## case for:
    //    | "IF" , expr_sans_asgn , "THEN" , expr , ["ELSE" , expr]
    try {
        bF.parserPrintdbgline('e', "Trying IF Expression...", lnum, recDepth);
        return bF._parseIfMode(lnum, tokens, states, recDepth + 1, false);
    }
    // if ParserError is raised, continue to apply other rules
    catch (e) {
        if (!(e instanceof ParserError)) throw e;
        bF.parserPrintdbgline('e', 'It was NOT!', lnum, recDepth);
    }

    /*************************************************************************/

    // ## case for:
    //    | kywd , expr (* kywd = ? words that exists on the list of predefined function that are not operators ? ; *)
    if (bS.builtin[headTkn] && headSta == "lit" && !bF._opPrc[headTkn] &&
        states[1] != "paren"
    ) {
        bF.parserPrintdbgline('e', 'Builtin Function Call w/o Paren', lnum, recDepth);

        return bF._parseFunctionCall(lnum, tokens, states, recDepth + 1);
    }

    /*************************************************************************/

    // ## case for:
    //    (* at this point, if OP is found in paren-level 0, skip function_call *)
    //    | function_call ;
    if (topmostOp === undefined) { // don't remove this IF statement!
        try {
            bF.parserPrintdbgline('e', "Trying Function Call...", lnum, recDepth);
            return bF._parseFunctionCall(lnum, tokens, states, recDepth + 1);
        }
        // if ParserError is raised, continue to apply other rules
        catch (e) {
            if (!(e instanceof ParserError)) throw e;
            bF.parserPrintdbgline('e', 'It was NOT!', lnum, recDepth);
        }
    }

    /*************************************************************************/

    // ## case for:
    //    | expr , op, expr
    //    | op_uni , expr
    // if operator is found, split by the operator and recursively parse the LH and RH
    if (topmostOp !== undefined) {
        bF.parserPrintdbgline('e', 'Operators', lnum, recDepth);

        if (ifMode && topmostOp == "=") throw lang.syntaxfehler(lnum, "'=' used on IF, did you mean '=='?");
        if (ifMode && topmostOp == ":") throw lang.syntaxfehler(lnum, "':' used on IF");


        // this is the AST we're going to build up and return
        // (other IF clauses don't use this)
        let treeHead = new BasicAST();
        treeHead.astLnum = lnum;
        treeHead.astValue = topmostOp;
        treeHead.astType = "op";

        // BINARY_OP?
        if (operatorPos > 0) {
            let subtknL = tokens.slice(0, operatorPos);
            let substaL = states.slice(0, operatorPos);
            let subtknR = tokens.slice(operatorPos + 1, tokens.length);
            let substaR = states.slice(operatorPos + 1, tokens.length);

            treeHead.astLeaves[0] = bF._parseExpr(lnum, subtknL, substaL, recDepth + 1);
            treeHead.astLeaves[1] = bF._parseExpr(lnum, subtknR, substaR, recDepth + 1);
        }
        else {
            if (topmostOp === "-") treeHead.astValue = "UNARYMINUS"
            else if (topmostOp === "+") treeHead.astValue = "UNARYPLUS"
            else if (topmostOp === "NOT") treeHead.astValue = "UNARYLOGICNOT"
            else if (topmostOp === "BNOT") treeHead.astValue = "UNARYBNOT"
            else throw new ParserError(`Unknown unary op '${topmostOp}'`)

            treeHead.astLeaves[0] = bF._parseExpr(lnum,
                tokens.slice(operatorPos + 1, tokens.length),
                states.slice(operatorPos + 1, states.length),
                recDepth + 1
            );
        }

        return treeHead;
    }

    /*************************************************************************/

    throw new ParserError("Expression cannot be parsed in "+lnum);
} // END of EXPR
/** Parses following EBNF rule:
      "IF" , expr_sans_asgn , "THEN" , stmt , ["ELSE" , stmt]
    | "IF" , expr_sans_asgn , "THEN" , expr , ["ELSE" , expr]
    if exprMode is true, only the latter will be used; former otherwise
 * @return: BasicAST
 */
bF._parseIfMode = function(lnum, tokens, states, recDepth, exprMode) {
    bF.parserPrintdbg2('/', lnum, tokens, states, recDepth);

    /*************************************************************************/

    let headTkn = tokens[0].toUpperCase();
    let headSta = states[0];

    let parseFunction = (exprMode) ? bF._parseExpr : bF._parseStmt

    let thenPos = -1;
    let elsePos = -1;
    let parenDepth = 0;
    let parenStart = -1;
    let parenEnd = -1;

    // scan for parens that will be used for several rules
    // also find nearest THEN and ELSE but also take parens into account
    for (let k = 0; k < tokens.length; k++) {
        // increase paren depth and mark paren start position
        if (tokens[k] == "(" && states[k] != "qot") {
            parenDepth += 1;
            if (parenStart == -1 && parenDepth == 1) parenStart = k;
        }
        // decrease paren depth
        else if (tokens[k] == ")" && states[k] != "qot") {
            if (parenEnd == -1 && parenDepth == 1) parenEnd = k;
            parenDepth -= 1;
        }

        if (parenDepth == 0) {
            if (-1 == thenPos && "THEN" == tokens[k].toUpperCase() && "lit" == states[k])
                thenPos = k;
            else if (-1 == elsePos && "ELSE" == tokens[k].toUpperCase() && "lit" == states[k])
                elsePos = k;
        }
    }

    // unmatched brackets, duh!
    if (parenDepth != 0) throw lang.syntaxfehler(lnum, lang.unmatchedBrackets);

    let treeHead = new BasicAST();
    treeHead.astLnum = lnum;

    // ## case for:
    //    "IF" , expr_sans_asgn , "THEN" , stmt , ["ELSE" , stmt]
    if ("IF" == headTkn && "lit" == headSta) {

        // "THEN" not found, raise error!
        if (thenPos == -1) throw lang.syntaxfehler(lnum, "IF without THEN");

        treeHead.astValue = "IF";
        treeHead.astType = "function";

        treeHead.astLeaves[0] = bF._parseExpr(lnum,
            tokens.slice(1, thenPos),
            states.slice(1, thenPos),
            recDepth + 1,
            true // if_equation mode
        );
        treeHead.astLeaves[1] = parseFunction(lnum,
            tokens.slice(thenPos + 1, (elsePos != -1) ? elsePos : tokens.length),
            states.slice(thenPos + 1, (elsePos != -1) ? elsePos : tokens.length),
            recDepth + 1
        );
        if (elsePos != -1)
            treeHead.astLeaves[2] = parseFunction(lnum,
                tokens.slice(elsePos + 1, tokens.length),
                states.slice(elsePos + 1, tokens.length),
                recDepth + 1
            );

        return treeHead;
    }

    throw new ParserError("not an IF "+(exprMode) ? "expression" : "statement");
} // END of IF
/** Parses following EBNF rule:
ident_tuple = "[" , ident , ["," , ident] , "]" ;
 * @return: BasicAST
 */
bF._parseTuple = function(lnum, tokens, states, recDepth) {
    bF.parserPrintdbg2(']', lnum, tokens, states, recDepth);
    
    /*************************************************************************/

    let parenDepth = 0;
    let parenStart = -1;
    let parenEnd = -1;
    let argSeps = []; // argseps collected when parenDepth == 0

    // Scan for unmatched parens and mark off the right operator we must deal with
    // every function_call need to re-scan because it is recursively called
    for (let k = 0; k < tokens.length; k++) {
        // increase paren depth and mark paren start position
        if (tokens[k] == "[" && states[k] != "qot") {
            parenDepth += 1;
            if (parenStart == -1 && parenDepth == 1) parenStart = k;
        }
        // decrease paren depth
        else if (tokens[k] == "]" && states[k] != "qot") {
            if (parenEnd == -1 && parenDepth == 1) parenEnd = k;
            parenDepth -= 1;
        }
        
        // where are the argument separators
        if (parenDepth == 1 && parenEnd == -1 && states[k] == "sep")
            argSeps.push(k);
        // break if we've got all the values we nedd
        if (parenStart != -1 && parenEnd != -1)
            break;
    }

    // unmatched brackets, duh!
    if (parenDepth != 0) throw lang.syntaxfehler(lnum, lang.unmatchedBrackets);

    if (parenStart != 0 || parenEnd != tokens.length - 1)
        throw new ParserError("not a Tuple expression");
    
    /*************************************************************************/
    
    let treeHead = new BasicAST();
    treeHead.astLnum = lnum;
    treeHead.astValue = undefined;
    treeHead.astType = "closure_args";

    // parse function arguments
    bF.parserPrintdbgline(']', 'Tuple arguments -- ', lnum, recDepth);
    let defunArgDeclSeps = argSeps.map(i => i-1).concat([parenEnd - 1]);
    bF.parserPrintdbgline(']', 'Tuple comma position: '+defunArgDeclSeps, lnum, recDepth);

    treeHead.astLeaves = defunArgDeclSeps.map(i=>bF._parseIdent(lnum, [tokens[i]], [states[i]], recDepth + 1));
    
    return treeHead;
}
/** Parses following EBNF rule:
function_call =
      ident , "(" , [expr , {argsep , expr} , [argsep]] , ")"
    | ident , expr , {argsep , expr} , [argsep] ;
 * @return: BasicAST
 */
bF._parseFunctionCall = function(lnum, tokens, states, recDepth) {
    bF.parserPrintdbg2("F", lnum, tokens, states, recDepth);

    /*************************************************************************/

    let parenDepth = 0;
    let parenStart = -1;
    let parenEnd = -1;
    let _argsepsOnLevelZero = []; // argseps collected when parenDepth == 0
    let _argsepsOnLevelOne = []; // argseps collected when parenDepth == 1
    let currentParenMode = []; // a stack; must be able to distinguish different kinds of parens as closures use [ this paren ]
    let depthsOfRoundParen = [];
    
    // Scan for unmatched parens and mark off the right operator we must deal with
    // every function_call need to re-scan because it is recursively called
    for (let k = 0; k < tokens.length; k++) {
        // increase paren depth and mark paren start position
        if (bF._isParenOpen(tokens[k]) && states[k] == "paren") {
            parenDepth += 1; currentParenMode.unshift(tokens[k]);
            if (currentParenMode[0] == '(') depthsOfRoundParen.push(parenDepth);
            if (parenStart == -1 && parenDepth == 1) parenStart = k;
        }
        // decrease paren depth
        else if (bF._isParenClose(tokens[k]) && states[k] == "paren") {
            if (!bF._isMatchingParen(currentParenMode[0], tokens[k]))
                throw lang.syntaxfehler(lnum, `Opening paren: ${currentParenMode[0]}, closing paren: ${tokens[k]}`); 
            
            if (parenEnd == -1 && parenDepth == 1) parenEnd = k;
            if (currentParenMode[0] == '(') depthsOfRoundParen.pop();
            parenDepth -= 1; currentParenMode.shift();
        }

        if (parenDepth == 0 && states[k] == "sep" && currentParenMode[0] === undefined)
            _argsepsOnLevelZero.push(k);
        if (parenDepth == depthsOfRoundParen[0] && states[k] == "sep" && currentParenMode[0] == "(")
            _argsepsOnLevelOne.push(k);
    }

    // unmatched brackets, duh!
    if (parenDepth != 0) throw lang.syntaxfehler(lnum, lang.unmatchedBrackets);
    let parenUsed = (parenStart == 1);
    // && parenEnd == tokens.length - 1);
    // if starting paren is found, just use it
    // this prevents "RND(~~)*K" to be parsed as [RND, (~~)*K]

    bF.parserPrintdbgline("F", `parenStart: ${parenStart}, parenEnd: ${parenEnd}`, lnum, recDepth);
    
    /*************************************************************************/

    // ## case for:
    //      ident , "(" , [expr , {argsep , expr} , [argsep]] , ")"
    //    | ident , expr , {argsep , expr} , [argsep] ;
    bF.parserPrintdbgline("F", `Function Call (parenUsed: ${parenUsed})`, lnum, recDepth);

    let treeHead = new BasicAST();
    treeHead.astLnum = lnum;

    // set function name and also check for syntax by deliberately parsing the word
    treeHead.astValue = bF._parseIdent(lnum, [tokens[0]], [states[0]], recDepth + 1).astValue; // always UPPERCASE

    // 5 8 11 [end]
    let argSeps = parenUsed ? _argsepsOnLevelOne : _argsepsOnLevelZero; // choose which "sep tray" to use
    bF.parserPrintdbgline("F", "argSeps = "+argSeps, lnum, recDepth);
    // 1 6 9 12
    let argStartPos = [1 + (parenUsed)].concat(argSeps.map(k => k+1));
    bF.parserPrintdbgline("F", "argStartPos = "+argStartPos, lnum, recDepth);
    // [1,5) [6,8) [9,11) [12,end)
    let argPos = argStartPos.map((s,i) => {return{start:s, end:(argSeps[i] || (parenUsed ? parenEnd : tokens.length) )}}); // use end of token position as separator position
    bF.parserPrintdbgline("F", "argPos = "+argPos.map(it=>`${it.start}/${it.end}`), lnum, recDepth);

    // check for trailing separator


    // recursively parse function arguments
    treeHead.astLeaves = argPos.map((x,i) => {
        bF.parserPrintdbgline("F", 'Function Arguments #'+(i+1), lnum, recDepth);

        // check for empty tokens
        if (x.end - x.start < 0) throw new ParserError("not a function call because it's malformed");

        return bF._parseExpr(lnum,
            tokens.slice(x.start, x.end),
            states.slice(x.start, x.end),
            recDepth + 1
        )}
    );
    treeHead.astType = "function";
    treeHead.astSeps = argSeps.map(i => tokens[i]);
    bF.parserPrintdbgline("F", "astSeps = "+treeHead.astSeps, lnum, recDepth);

    return treeHead;
}
bF._parseIdent = function(lnum, tokens, states, recDepth) {
    bF.parserPrintdbg2('i', lnum, tokens, states, recDepth);

    if (!Array.isArray(tokens) && !Array.isArray(states)) throw new ParserError("Tokens and states are not array");
    if (tokens.length != 1 || states[0] != "lit") throw new ParserError(`illegal tokens '${tokens}' with states '${states}' in ${lnum}`);

    let treeHead = new BasicAST();
    treeHead.astLnum = lnum;
    treeHead.astValue = tokens[0].toUpperCase();
    treeHead.astType = "lit";

    return treeHead;
}
/**
 * @return: BasicAST
 */
bF._parseLit = function(lnum, tokens, states, recDepth, functionMode) {
    bF.parserPrintdbg2('i', lnum, tokens, states, recDepth);

    if (!Array.isArray(tokens) && !Array.isArray(states)) throw new ParserError("Tokens and states are not array");
    if (tokens.length != 1) throw new ParserError("parseLit 1");

    let treeHead = new BasicAST();
    treeHead.astLnum = lnum;
    treeHead.astValue = ("qot" == states[0]) ? tokens[0] : tokens[0].toUpperCase();
    treeHead.astType = ("qot" == states[0]) ? "string" :
        ("num" == states[0]) ? "num" :
        (functionMode) ? "function" : "lit";

    return treeHead;
}
/**
 * @return: Array of [recurseIndex, orderlyIndex], where recurseIndex is in reverse and orderlyIndex is not
 */
bF._findDeBruijnIndex = function(varname, offset) {
    let recurseIndex = -1;
    let orderlyIndex = -1;
    for (recurseIndex = 0; recurseIndex < lambdaBoundVars.length; recurseIndex++) {
        orderlyIndex = lambdaBoundVars[recurseIndex].findIndex(it => it == varname);
        if (orderlyIndex != -1)
            return [recurseIndex + (offset || 0), orderlyIndex];
    }
    throw new ParserError("Unbound variable: "+varname);
}
/**
 * @return: BasicAST
 */
bF._pruneTree = function(lnum, tree, recDepth) {    
    if (tree === undefined) return;
    
    if (DBGON) {
        serial.println("[Parser.PRUNE] pruning following subtree, lambdaBoundVars = "+Object.entries(lambdaBoundVars)); // theLambdaBoundVars() were not formatted for this use case!
        serial.println(astToString(tree));
        if (isAST(tree) && isAST(tree.astValue)) {
            serial.println("[Parser.PRUNE] unpacking astValue:");
            serial.println(astToString(tree.astValue));
        }
    }
    
    let defunName = undefined;
    
    // catch all the bound variables for function definition
    if (tree.astType == "op" && tree.astValue == "~>" || tree.astType == "function" && tree.astValue == "DEFUN") {
        
        let nameTree = tree.astLeaves[0];
        if (tree.astValue == "DEFUN") {
            defunName = nameTree.astValue;
            
            if (DBGON) {
                serial.println("[Parser.PRUNE.~>] met DEFUN, function name: "+defunName);
            }
        }
        let vars = nameTree.astLeaves.map((it, i) => {
            if (it.astType !== "lit") throw new ParserError("Malformed bound variable for function definition; tree:\n"+astToString(nameTree));
            return it.astValue;
        });//.reverse();
        
        lambdaBoundVars.unshift(vars);
        
        if (DBGON) {
            serial.println("[Parser.PRUNE.~>] added new bound variables: "+Object.entries(lambdaBoundVars));
        }
    }
    // simplify UNARYMINUS(num) to -num
    else if (tree.astValue == "UNARYMINUS" && tree.astType == "op" &&
        tree.astLeaves[1] === undefined && tree.astLeaves[0] !== undefined && tree.astLeaves[0].astType == "num"
    ) {
        tree.astValue = -(tree.astLeaves[0].astValue);
        tree.astType = "num";
        tree.astLeaves = [];
    }
    else if (tree.astValue == "UNARYPLUS" && tree.astType == "op" &&
        tree.astLeaves[1] === undefined && tree.astLeaves[0] !== undefined && tree.astLeaves[0].astType == "num"
    ) {
        tree.astValue = +(tree.astLeaves[0].astValue);
        tree.astType = "num";
        tree.astLeaves = [];
    }
    
    
    // depth-first run
    if (tree.astLeaves[0] != undefined) {
        tree.astLeaves.forEach(it => bF._pruneTree(lnum, it, recDepth + 1));
    }
    
    
    if (tree.astType == "op" && tree.astValue == "~>" || tree.astType == "function" && tree.astValue == "DEFUN") {
        
        if (tree.astLeaves.length !== 2) throw lang.syntaxfehler(lnum, tree.astLeaves.length+lang.aG);
        
        let nameTree = tree.astLeaves[0];
        let exprTree = tree.astLeaves[1];
        
        // test print new tree
        if (DBGON) {
            serial.println("[Parser.PRUNE.~>] closure bound variables: "+Object.entries(lambdaBoundVars));
        }
        
        // rename the parameters
        bF._recurseApplyAST(exprTree, (it) => {
            if (it.astType == "lit" || it.astType == "function") {                
                // check if parameter name is valid
                // if the name is invalid, regard it as a global variable (i.e. do nothing)
                try {
                    let dbi = bF._findDeBruijnIndex(it.astValue);
                    
                    if (DBGON) {
                        serial.println(`index for ${it.astValue}: ${dbi}`)
                    }
                    
                    
                    it.astValue = dbi;
                    it.astType = "defun_args";
                }
                catch (_) {}
            }
        });
        
        tree.astType = "usrdefun";
        tree.astValue = exprTree;
        tree.astLeaves = [];
        
        lambdaBoundVars.shift();
    }
    
    // for DEFUNs, build assign tree such that:
    //    DEFUN F lambda
    // turns into:
    //    F=(lambda)
    if (defunName) {
        let nameTree = new BasicAST();
        nameTree.astLnum = tree.astLnum;
        nameTree.astType = "lit";
        nameTree.astValue = defunName;
        
        let newTree = new BasicAST();
        newTree.astLnum = tree.astLnum;
        newTree.astType = "op";
        newTree.astValue = "=";
        newTree.astLeaves = [nameTree, tree];
        
        tree = newTree;
        
        if (DBGON) {
            serial.println(`[Parser.PRUNE] has DEFUN, function name: ${defunName}`);
        }
    }
    
    if (DBGON) {
        serial.println("[Parser.PRUNE] pruned subtree:");
        serial.println(astToString(tree));
        if (isAST(tree) && isAST(tree.astValue)) {
            serial.println("[Parser.PRUNE] unpacking astValue:");
            serial.println(astToString(tree.astValue));
        }
        
        serial.println("======================================================\n");
    }
    
    return tree;
}

// ## USAGE OF lambdaBoundVars IN PARSEMODE ENDS HERE ##

// @return is defined in BasicAST
let JStoBASICtype = function(object) {
    if (typeof object === "boolean") return "bool";
    else if (object === undefined) return "null";
    else if (object.arrName !== undefined) return "internal_arrindexing_lazy";
    else if (object.asgnVarName !== undefined) return "internal_assignment_object";
    else if (isGenerator(object)) return "generator";
    else if (isAST(object)) return "usrdefun";
    else if (isMonad(object)) return "monad";
    else if (Array.isArray(object)) return "array";
    else if (isNumable(object)) return "num";
    else if (typeof object === "string" || object instanceof String) return "string";
    // buncha error msgs
    else throw Error("BasicIntpError: un-translatable object with typeof "+(typeof object)+",\ntoString = "+object+",\nentries = "+Object.entries(object));
}
let SyntaxTreeReturnObj = function(type, value, nextLine) {
    if (nextLine === undefined || !Array.isArray(nextLine))
        throw Error("TODO change format of troNextLine to [linenumber, stmtnumber]")

    this.troType = type;
    this.troValue = value;
    this.troNextLine = nextLine;
}
let JumpObj = function(targetLnum, targetStmtNum, fromLnum, rawValue) {
    this.jmpNext = [targetLnum, targetStmtNum];
    this.jmpFrom = fromLnum;
    this.jmpReturningValue = rawValue;
}
bF._makeRunnableFunctionFromExprTree = function(lnum, stmtnum, expression, args, recDepth, _debugExec, recWedge) {
    // register variables
    let defunArgs = args.map(it => {
        let rit = resolve(it);
        return [JStoBASICtype(rit), rit];
    });//.reverse();
    lambdaBoundVars.unshift(defunArgs);
    
    if (_debugExec) {
        serial.println(recWedge+"usrdefun dereference");
        serial.println(recWedge+"usrdefun dereference function: ");
        serial.println(astToString(expression));
        serial.println(recWedge+"usrdefun dereference bound vars: "+theLambdaBoundVars());
    }
    
    // insert bound variables to its places
    let bindVar = function(tree, recDepth) {
        bF._recurseApplyAST(tree, it => {
            
            if (_debugExec) {
                serial.println(recWedge+`usrdefun${recDepth} trying to bind some variables to:`);
                serial.println(astToString(it));
            }
            
            if (it.astType == "defun_args") {
                let recIndex = it.astValue[0] - recDepth;
                let varIndex = it.astValue[1];
                
                if (_debugExec) {
                    serial.println(recWedge+`usrdefun${recDepth} bindvar d(${recIndex},${varIndex})`);
                }
                
                let theVariable = undefined;
                try {
                    theVariable = lambdaBoundVars[recIndex][varIndex];
                }
                catch (e0) {}
                
                // this will make partial applying work, but completely remove the ability of catching errors...
                if (theVariable !== undefined) {
                    it.astValue = theVariable[1];
                    it.astType = theVariable[0];
                }
                
                if (_debugExec) {
                    serial.println(recWedge+`usrdefun${recDepth} the bindvar: ${theVariable}`);
                    serial.println(recWedge+`usrdefun${recDepth} modified tree:`);
                    serial.println(astToString(it));
                }
            }
            // function in a function
            else if (it.astType == "usrdefun") {
                bindVar(it.astValue, recDepth + 1);
            }
        });
    };bindVar(expression, 0);
    
    
    if (_debugExec) {
        serial.println(recWedge+"usrdefun dereference final tree:");
        serial.println(astToString(expression));
    }
    
    return bS.getDefunThunk(expression, true);
}
/**
 * @param lnum line number of BASIC
 * @param syntaxTree BasicAST
 * @param recDepth recursion depth used internally
 *
 * @return syntaxTreeReturnObject if recursion is escaped
 */
bF._troNOP = function(lnum, stmtnum) { return new SyntaxTreeReturnObj("null", undefined, [lnum, stmtnum+1]); }
bF._executeSyntaxTree = function(lnum, stmtnum, syntaxTree, recDepth) {
    if (syntaxTree == undefined) return bF._troNOP(lnum, stmtnum);
    if (syntaxTree.astLeaves === undefined && syntaxTree.astValue === undefined) {
        throw new InternalError("not a syntax tree");
    }
    
    if (lnum === undefined || stmtnum === undefined) throw Error(`Line or statement number is undefined: (${lnum},${stmtnum})`);

    let _debugExec = (!PROD) && true;
    let _debugPrintCurrentLine = (!PROD) && true;
    let recWedge = ">".repeat(recDepth+1) + " ";
    let tearLine = "\n  =====ExecSyntaxTree=====  "+("<".repeat(recDepth+1))+"\n";
    
    if (_debugExec || _debugPrintCurrentLine) serial.println(recWedge+`@@ EXECUTE ${lnum}:${stmtnum} @@`);
    if (_debugPrintCurrentLine) {
        serial.println("Syntax Tree in "+lnum+":");
        serial.println(astToString(syntaxTree));
    }

    let callingUsrdefun = (syntaxTree.astType == "usrdefun" && syntaxTree.astLeaves[0] !== undefined);
    // do NOT substitute (syntaxTree.astType == "usrdefun") with isAST; doing so will break (=) operator
    // calling usrdefun without any args will make leaves[0] to be null-node but not undefined
    // funseq-monad will be dealt with on (func === undefined) branch
    
    if (syntaxTree.astValue == undefined && syntaxTree.mVal == undefined) { // empty meaningless parens
        if (syntaxTree.astLeaves.length > 1) throw Error("WTF");
        return bF._executeSyntaxTree(lnum, stmtnum, syntaxTree.astLeaves[0], recDepth);
    }
    // array indexing in the tree (caused by indexing array within recursive DEFUN)
    else if (syntaxTree.astType == "array" && syntaxTree.astLeaves[0] !== undefined) {
        let indexer = bS.getArrayIndexFun(lnum, stmtnum, "substituted array", syntaxTree.astValue);
        let args = syntaxTree.astLeaves.map(it => bF._executeSyntaxTree(lnum, stmtnum, it, recDepth + 1));
        let retVal = indexer(lnum, stmtnum, args);
        if (_debugExec) serial.println(recWedge+`indexing substituted array(${Object.entries(args)}) = ${Object.entries(retVal)}`);
        return new SyntaxTreeReturnObj(
                JStoBASICtype(retVal),
                retVal,
                [lnum, stmtnum + 1]
        );
    }
    // closure
    // type: closure_args ~> (expr)
    else if (syntaxTree.astType == "op" && syntaxTree.astValue == "~>") {
        throw new InternalError("Untended closure"); // closure definition must be 'pruned' by the parser
    }
    else if (syntaxTree.astType == "function" && syntaxTree.astValue == "DEFUN") {
        throw new InternalError("Untended DEFUN"); // DEFUN must be 'pruned' by the parser
    }
    else if (syntaxTree.astType == "function" || syntaxTree.astType == "op" || callingUsrdefun) {
        if (_debugExec) serial.println(recWedge+"function|operator");
        if (_debugExec) serial.println(recWedge+astToString(syntaxTree));
        let funcName = (typeof syntaxTree.astValue.toUpperCase == "function") ? syntaxTree.astValue.toUpperCase() : "(usrdefun)";
        let lambdaBoundVarsAppended = (callingUsrdefun);
        let func = (callingUsrdefun)
                ? bF._makeRunnableFunctionFromExprTree(
                    lnum, stmtnum,
                    cloneObject(syntaxTree.astValue),
                    syntaxTree.astLeaves.map(it => bF._executeSyntaxTree(lnum, stmtnum, it, recDepth + 1)), // the args
                    recDepth, _debugExec, recWedge
                )
            : (bS.builtin[funcName] === undefined)
                ? undefined
            : (!DBGON && bS.builtin[funcName].debugonly) ? "NO_DBG4U" : (PROD && bS.builtin[funcName].noprod) ? "NO_PRODREADY" : bS.builtin[funcName].f;

        if (func === "NO_DBG4U") throw lang.syntaxfehler(lnum);
        if (func === "NO_PRODREADY") throw lang.syntaxfehler(lnum);

        if ("IF" == funcName) {
            if (syntaxTree.astLeaves.length != 2 && syntaxTree.astLeaves.length != 3) throw lang.syntaxfehler(lnum);
            var testedval = bF._executeSyntaxTree(lnum, stmtnum, syntaxTree.astLeaves[0], recDepth + 1);

            if (_debugExec) {
                serial.println(recWedge+"testedval:");
                serial.println(recWedge+"type="+testedval.troValue.astType);
                serial.println(recWedge+"value="+testedval.troValue.astValue);
                serial.println(recWedge+"nextLine="+testedval.troValue.astNextLine);
            }

            try {
                var iftest = bS.builtin["TEST"].f(lnum, stmtnum, [testedval]);

                let r = (!iftest && syntaxTree.astLeaves[2] !== undefined) ?
                        bF._executeSyntaxTree(lnum, stmtnum, syntaxTree.astLeaves[2], recDepth + 1)
                    : (iftest) ?
                        bF._executeSyntaxTree(lnum, stmtnum, syntaxTree.astLeaves[1], recDepth + 1)
                    : bF._troNOP(lnum, stmtnum);
                
                if (_debugExec) serial.println(tearLine);
                return r;
            }
            catch (e) {
                serial.printerr(`${e}\n${e.stack || "Stack trace undefined"}`);
                throw lang.errorinline(lnum, "TEST", e);
            }
        }
        else if ("ON" == funcName) {
            if (syntaxTree.astLeaves.length < 3) throw lang.badFunctionCallFormat(lnum);

            let testValue = bF._executeSyntaxTree(lnum, stmtnum, syntaxTree.astLeaves[0], recDepth + 1);
            let functionName = syntaxTree.astLeaves[1].astValue;
            let arrays = [];
            for (let k = 2; k < syntaxTree.astLeaves.length; k++)
                arrays.push(bF._executeSyntaxTree(lnum, stmtnum, syntaxTree.astLeaves[k], recDepth + 1));

            try  {
                let r = bS.builtin["ON"].f(lnum, stmtnum, [functionName, testValue].concat(arrays))
                let r2 = new SyntaxTreeReturnObj(JStoBASICtype(r.jmpReturningValue), r.jmpReturningValue, r.jmpNext);
                if (_debugExec) serial.println(tearLine);
                return r2;
            }
            catch (e) {
                serial.printerr(`${e}\n${e.stack || "Stack trace undefined"}`);
                throw lang.errorinline(lnum, "ON error", e);
            }
        }
        else {
            let args = syntaxTree.astLeaves.map(it => bF._executeSyntaxTree(lnum, stmtnum, it, recDepth + 1));
            
            if (_debugExec) {
                serial.println(recWedge+"fn call name: "+funcName);
                serial.println(recWedge+"fn call args: "+(args.map(it => (it == undefined) ? it : (it.troType+" "+it.troValue)).join(", ")));
            }
                        
            // func not in builtins (e.g. array access, user-defined function defuns)
            if (func === undefined) {
                var someVar = bS.vars[funcName];

                if (DBGON) {
                    serial.println(recWedge+`variable dereference of '${funcName}' : ${someVar.bvLiteral} (bvType: ${someVar.bvType})`);
                    if (typeof someVar.bvLiteral == "object")
                        serial.println(recWedge+"variable as an object : "+Object.entries(someVar.bvLiteral));
                }

                if (someVar === undefined) {
                    throw lang.syntaxfehler(lnum, funcName + " is undefined");
                }
                else if ("array" == someVar.bvType) {
                    func = bS.getArrayIndexFun(lnum, stmtnum, funcName, someVar.bvLiteral);
                }
                else if ("usrdefun" == someVar.bvType) {
                    // dereference usrdefun
                    let expression = cloneObject(someVar.bvLiteral);
                    lambdaBoundVarsAppended = true;
                    func = bF._makeRunnableFunctionFromExprTree(lnum, stmtnum, expression, args, recDepth, _debugExec, recWedge);
                }
                else if ("monad" == someVar.bvType) {
                    func = getMonadEvalFun(someVar.bvLiteral);
                }
                else {
                    throw lang.syntaxfehler(lnum, funcName + " is not a function or an array");
                }
            }
            
            // call whatever the 'func' has whether it's builtin or we just made shit up right above
            if (func === undefined) {
                serial.printerr(lnum+` ${funcName} is undefined`);
                throw lang.syntaxfehler(lnum, funcName + " is undefined");
            }

            let funcCallResult = func(lnum, stmtnum, args, syntaxTree.astSeps);
            
            if (funcCallResult instanceof SyntaxTreeReturnObj) return funcCallResult;
            
            let retVal = (funcCallResult instanceof JumpObj) ? funcCallResult.jmpReturningValue : funcCallResult;
            
            let theRealRet = new SyntaxTreeReturnObj(
                JStoBASICtype(retVal),
                retVal,
                (funcCallResult instanceof JumpObj) ? funcCallResult.jmpNext : [lnum, stmtnum + 1]
            );
            
            // unregister variables
            if (lambdaBoundVarsAppended) lambdaBoundVars.shift();
            
            if (_debugExec) serial.println(tearLine);
            return theRealRet;
        }
    }
    else if (syntaxTree.astType == "defun_args") {
        if (_debugExec) {
            serial.println(recWedge+"defun_args lambda bound vars: "+(lambdaBoundVars === undefined) ? undefined : theLambdaBoundVars());
            serial.println(recWedge+"defun_args defun args: "+syntaxTree.astValue);
        }
        let recIndex = syntaxTree.astValue[0];
        let varIndex = syntaxTree.astValue[1];
        let theVar = lambdaBoundVars[recIndex, varIndex];
        if (_debugExec) {
            serial.println(recWedge+"defun_args thevar: "+(theVar === undefined) ? undefined : Object.entries(theVar));
            serial.println(tearLine);
        }
        return theVar;
    }
    else if (syntaxTree.astType == "num") {
        if (_debugExec) serial.println(recWedge+"num "+(tonum(syntaxTree.astValue)));
        let r = new SyntaxTreeReturnObj(syntaxTree.astType, tonum(syntaxTree.astValue), [lnum, stmtnum + 1]);
        if (_debugExec) serial.println(tearLine);
        return r;
    }
    else if (syntaxTree.astType == "lit" || literalTypes.includes(syntaxTree.astType)) {
        if (_debugExec) {
            serial.println(recWedge+"literal with astType: "+syntaxTree.astType+", astValue: "+syntaxTree.astValue);
            if (isAST(syntaxTree.astValue)) {
                serial.println(recWedge+"astValue is a tree, unpacking: \n"+astToString(syntaxTree.astValue));
            }
        }
        let r = new SyntaxTreeReturnObj(syntaxTree.astType, syntaxTree.astValue, [lnum, stmtnum + 1]);
        if (_debugExec) serial.println(tearLine);
        return r;
    }
    else if (syntaxTree.astType == "null") {
        if (_debugExec) serial.println(recWedge+"null")
        let r = bF._executeSyntaxTree(lnum, stmtnum, syntaxTree.astLeaves[0], recDepth + 1);
        if (_debugExec) serial.println(tearLine);
        return r;
    }
    else {
        serial.println(recWedge+"Parsing error in "+lnum);
        serial.println(recWedge+astToString(syntaxTree));
        throw Error("Parsing error");
    }
}; // END OF bF._executeSyntaxTree
// @return ARRAY of BasicAST
bF._interpretLine = function(lnum, cmd) {
    let _debugprintHighestLevel = false;

    if (cmd.toUpperCase().startsWith("REM")) {
        if (_debugprintHighestLevel) serial.println(lnum+" "+cmd);
        return undefined;
    }

    // TOKENISE
    let tokenisedObject = bF._tokenise(lnum, cmd);
    let tokens = tokenisedObject.tokens;
    let states = tokenisedObject.states;


    // ELABORATION : distinguish numbers and operators from literals
    let newtoks = bF._parserElaboration(lnum, tokens, states);
    tokens = newtoks.tokens;
    states = newtoks.states;
    
    // PARSING (SYNTAX ANALYSIS)
    let syntaxTrees = bF._parseTokens(lnum, tokens, states).map(it => {
        if (lambdaBoundVars.length != 0)
            throw new InternalError("lambdaBoundVars not empty");
        return bF._pruneTree(lnum, it, 0)
    });

    if (_debugprintHighestLevel) {
        syntaxTrees.forEach((t,i) => {
            serial.println("\nParsed Statement #"+(i+1));
            serial.println(astToString(t));
        });
    }

    return syntaxTrees;
}; // end INTERPRETLINE
// @return [next line number, next statement number]
bF._executeAndGet = function(lnum, stmtnum, syntaxTree) {
    if (lnum === undefined || stmtnum === undefined) throw Error(`Line or statement number is undefined: (${lnum},${stmtnum})`);

    // EXECUTE
    try {
        if (lambdaBoundVars.length != 0) throw new InternalError();
        var execResult = bF._executeSyntaxTree(lnum, stmtnum, syntaxTree, 0);

        if (DBGON) serial.println(`Line ${lnum} TRO: ${Object.entries(execResult)}`);

        return execResult.troNextLine;
    }
    catch (e) {
        serial.printerr(`ERROR on ${lnum}:${stmtnum} -- PARSE TREE:\n${astToString(syntaxTree)}\nERROR CONTENTS:\n${e}\n${e.stack || "Stack trace undefined"}`);
        throw e;
    }
};
bF._basicList = function(v, i, arr) {
    if (i < 10) print(" ");
    if (i < 100) print(" ");
    print(i);
    print(" ");
    println(v);
};
bF.list = function(args) { // LIST function
    if (args.length == 1) {
        cmdbuf.forEach(bF._basicList);
    }
    else if (args.length == 2) {
        if (cmdbuf[args[1]] !== undefined)
            bF._basicList(cmdbuf[args[1]], args[1], undefined);
    }
    else {
        var lastIndex = (args[2] === ".") ? cmdbuf.length - 1 : (args[2] | 0);
        var i = 0;
        for (i = args[1]; i <= lastIndex; i++) {
            var cmd = cmdbuf[i];
            if (cmd !== undefined) {
                bF._basicList(cmd, i, cmdbuf);
            }
        }
    }
};
bF.system = function(args) { // SYSTEM function
    tbasexit = true;
};
bF.new = function(args) { // NEW function
    if (args) cmdbuf = [];
    bS.vars = initBvars();
    gotoLabels = {};
    lambdaBoundVars = [];
    DATA_CONSTS = [];
    DATA_CURSOR = 0;
    INDEX_BASE = 0;
};
bF.renum = function(args) { // RENUM function
    var newcmdbuf = [];
    var linenumRelation = [[]];
    var cnt = 10;
    for (var k = 0; k < cmdbuf.length; k++) {
        if (cmdbuf[k] !== undefined) {
            newcmdbuf[cnt] = cmdbuf[k].trim();
            linenumRelation[k] = cnt;
            cnt += 10;
        }
    }
    // deal with goto/gosub line numbers
    for (k = 0; k < newcmdbuf.length; k++) {
        if (newcmdbuf[k] !== undefined && newcmdbuf[k].toLowerCase().startsWith("goto ")) {
            newcmdbuf[k] = "GOTO " + linenumRelation[newcmdbuf[k].match(reNum)[0]];
        }
        else if (newcmdbuf[k] !== undefined && newcmdbuf[k].toLowerCase().startsWith("gosub ")) {
            newcmdbuf[k] = "GOSUB " + linenumRelation[newcmdbuf[k].match(reNum)[0]];
        }
        else if (newcmdbuf[k] !== undefined && newcmdbuf[k].toLowerCase().startsWith("breakto ")) {
            newcmdbuf[k] = "BREAKTO " + linenumRelation[newcmdbuf[k].match(reNum)[0]];
        }
    }
    cmdbuf = newcmdbuf.slice(); // make shallow copy

    // recalculate memory footprint
    cmdbufMemFootPrint = 0;
    cmdbuf.forEach((v, i, arr) =>
        cmdbufMemFootPrint += ("" + i).length + 1 + v.length
    );
};
bF.fre = function(args) {
    println(vmemsize - getUsedMemSize());
};
bF.tron = function(args) {
    TRACEON = true;
};
bF.troff = function(args) {
    TRACEON = false;
};
bF.delete = function(args) {
    if (args.length != 2 && args.length != 3) throw lang.syntaxfehler();
    
    // stupid Javascript can't even Array.prototype.remove(int)
    let start = 0; let end = 0;
    if (args.length == 2) {
        if (!isNumable(args[1])) throw lang.badFunctionCallFormat();
        start = args[1]|0;
        end = args[1]|0;
    }
    else {
        if (!isNumable(args[1]) && !isNumable(args[2])) throw lang.badFunctionCallFormat();
        start = args[1]|0;
        end = args[2]|0;
    }
    
    let newcmdbuf = [];
    cmdbuf.forEach((v,i) => {if (i < start || i > end) newcmdbuf[i]=v});
    cmdbuf = newcmdbuf;
};
bF.cls = function(args) {
    con.clear();
}
bF.prescanStmts = ["DATA","LABEL"];
bF.run = function(args) { // RUN function
    bF.new(false);

    let programTrees = [];
    // pre-build the trees
    prescan = true;
    cmdbuf.forEach((linestr, linenum) => {
        let trees = bF._interpretLine(linenum, linestr.trim());
        programTrees[linenum] = trees
        // do prescan job (data, label, etc)
        if (trees !== undefined) {
            trees.forEach((t, i) => {
                if (t !== undefined && bF.prescanStmts.includes(t.astValue)) {
                    bF._executeAndGet(linenum, i, t);
                }
            })
        }
    });
    prescan = false;

    if (!PROD && DBGON) {
        serial.println("[BASIC] final DATA: "+DATA_CONSTS);
    }

    // actually execute the program
    let lnum = 1;
    let stmtnum = 0;
    let oldnum = 1;
    let tree = undefined;
    do {
        if (programTrees[lnum] !== undefined) {
            if (TRACEON) {
                //print(`[${lnum}]`);
                serial.println("[BASIC] Line "+lnum);
            }

            oldnum = lnum;
            tree = (programTrees[lnum] !== undefined) ? programTrees[lnum][stmtnum] : undefined;

            if (tree !== undefined) {
                let nextObj = bF._executeAndGet(lnum, stmtnum, tree);
                lnum = nextObj[0];
                stmtnum = nextObj[1];
            }
            else {
                lnum += 1;
                stmtnum = 0;
            }
        }
        else {
            lnum += 1;
        }
        if (lnum < 0) throw lang.badNumberFormat;
        if (con.hitterminate()) {
            println("Break in "+oldnum);
            break;
        }
    } while (lnum < cmdbuf.length)
    con.resetkeybuf();
};
bF.save = function(args) { // SAVE function
    if (args[1] === undefined) throw lang.missingOperand;
    if (!args[1].toUpperCase().endsWith(".BAS"))
        args[1] += ".bas";
    fs.open(args[1], "W");
    var sb = "";
    cmdbuf.forEach((v, i) => sb += i+" "+v+"\n");
    fs.write(sb);
};
bF.load = function(args) { // LOAD function
    if (args[1] === undefined) throw lang.missingOperand;
    var fileOpened = fs.open(args[1], "R");
    
        
    if (replUsrConfirmed || cmdbuf.length == 0) {
        if (!fileOpened) {
            fileOpened = fs.open(args[1]+".BAS", "R");
        }
        if (!fileOpened) {
            fileOpened = fs.open(args[1]+".bas", "R");
        }
        if (!fileOpened) {
            throw lang.noSuchFile;
            return;
        }
        var prg = fs.readAll();

        // reset the environment
        bF.new(true);

        // read the source
        prg.split('\n').forEach((line) => {
            var i = line.indexOf(" ");
            var lnum = line.slice(0, i);
            if (isNaN(lnum)) throw lang.illegalType();
            cmdbuf[lnum] = line.slice(i + 1, line.length);
        });
    }
    else {
        replCmdBuf = ["load"].concat(args);
        println("Unsaved program will be lost, are you sure? (type 'yes' to confirm)");
    }
};
bF.yes = function() {
    if (replCmdBuf.length > 0) {
        replUsrConfirmed = true;
        
        bF[replCmdBuf[0].toLowerCase()](replCmdBuf.slice(1, replCmdBuf.length));
        
        replCmdBuf = [];
        replUsrConfirmed = false;
    }
    else {
        throw lang.syntaxfehler("interactive", "nothing to confirm!");
    }
};
bF.catalog = function(args) { // CATALOG function
    if (args[1] === undefined) args[1] = "\\";
    var pathOpened = fs.open(args[1], 'R');
    if (!pathOpened) {
        throw lang.noSuchFile;
        return;
    }
    var port = _BIOS.FIRST_BOOTABLE_PORT[0];
    com.sendMessage(port, "LIST");
    println(com.pullMessage(port));
};
Object.freeze(bF);

if (exec_args !== undefined && exec_args[1] !== undefined) {
    bF.load(["load", exec_args[1]]);
    try {
        bF.run();
        return 0;
    }
    catch (e) {
        serial.printerr(`${e}\n${e.stack || "Stack trace undefined"}`);
        println(e);
    }
}

while (!tbasexit) {
    var line = sys.read().trim();

    cmdbufMemFootPrint += line.length;

    if (reLineNum.test(line)) {
        var i = line.indexOf(" ");
        cmdbuf[line.slice(0, i)] = line.slice(i + 1, line.length);
    }
    else if (line.length > 0) {
        cmdbufMemFootPrint -= line.length;
        var cmd = line.split(" ");
        if (bF[cmd[0].toLowerCase()] === undefined) {
            serial.printerr("Unknown command: "+cmd[0].toLowerCase());
            println(lang.syntaxfehler());
        }
        else {
            try {
                bF[cmd[0].toLowerCase()](cmd);
            }
            catch (e) {
                serial.printerr(`${e}\n${e.stack || "Stack trace undefined"}`);
                println(e);
            }
        }

        println(prompt);
    }
}

0;
