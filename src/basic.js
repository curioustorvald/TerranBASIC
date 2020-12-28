// Created by CuriousTorvald on 2020-05-19
// Version 1.0 Release Date 2020-12-28

/*
Copyright (c) 2020 CuriousTorvald

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

const THEVERSION = "1.0";

const PROD = true;
let INDEX_BASE = 0;
let TRACEON = (!PROD) && true;
let DBGON = (!PROD) && true;
let DATA_CURSOR = 0;
let DATA_CONSTS = [];
const DEFUNS_BUILD_DEFUNS = true;
const BASIC_HOME_PATH = "/home/basic/"

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

/* if string can be FOR REAL cast to number */
function isNumable(s) {
    return s !== undefined && (typeof s.trim == "function" && s.trim() !== "" || s.trim == undefined) && !isNaN(s);
}

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
lang.badFunctionCallFormat = function(reason) {
    return Error("Illegal function call" + ((reason) ? ": "+reason : ""));
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

    Object.entries(bStatus.vars).forEach((pair, i) => {
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
let reNumber = /([0-9]*[.][0-9]+[eE]*[\-+0-9]*[fF]*|[0-9]+[.eEfF][0-9+\-]*[fF]?)|([0-9_]+)|(0[Xx][0-9A-Fa-f_]+)|(0[Bb][01_]+)/;
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
 * @see bStatus.builtin["="]
 */
let BasicVar = function(literal, type) {
    this.bvLiteral = literal;
    this.bvType = type;
}
// Abstract Syntax Tree
// creates empty tree node
let astToString = function(ast, depth) {
    let l__ = String.fromCharCode(0x2502,32);
    let recDepth = depth || 0;
    if (ast === undefined || ast.astType === undefined) return "";
    var sb = "";
    var marker = ("lit" == ast.astType) ? "i" :
                 ("op" == ast.astType) ? String.fromCharCode(0xB1) :
                 ("string" == ast.astType) ? String.fromCharCode(0xB6) :
                 ("num" == ast.astType) ? String.fromCharCode(0xA2) :
                 ("array" == ast.astType) ? "[" :
                 ("defun_args" === ast.astType) ? String.fromCharCode(0x3B4) : String.fromCharCode(0x192);
    sb += l__.repeat(recDepth) + marker+" Line "+ast.astLnum+" ("+ast.astType+")\n";
    sb += l__.repeat(recDepth+1) + "leaves: "+(ast.astLeaves.length)+"\n";
    sb += l__.repeat(recDepth+1) + "value: "+ast.astValue+" (type: "+typeof ast.astValue+")\n";
    for (var k = 0; k < ast.astLeaves.length; k++) {
        sb += astToString(ast.astLeaves[k], recDepth + 1);
        sb += l__.repeat(recDepth+1) + " " + ast.astSeps[k] + "\n";
    }
    sb += l__.repeat(recDepth)+String.fromCharCode(0x2570)+String.fromCharCode(0x2500).repeat(13)+'\n';
    return sb;
}
let BasicAST = function() {
    this.astLnum = 0;
    this.astLeaves = [];
    this.astSeps = [];
    this.astValue = undefined;
    this.astType = "null"; // lit, op, string, num, array, function, null, defun_args (! NOT usrdefun !)
}
let literalTypes = ["string", "num", "bool", "array", "generator", "usrdefun"];
/*
@param variable SyntaxTreeReturnObj, of which  the 'troType' is defined in BasicAST.
@return a value, if the input type if string or number, its literal value will be returned. Otherwise will search the
        BASIC variable table and return the literal value of the BasicVar; undefined will be returned if no such var exists.
*/
let resolve = function(variable) {
    // head error checking
    if (variable.troType === undefined) {
        // primitves types somehow injected from elsewhere (main culprit: MAP)
        //throw Error(`BasicIntpError: trying to resolve unknown object '${variable}' with entries ${Object.entries(variable)}`);

        if (isNumable(variable)) return variable*1;
        if (Array.isArray(variable)) return variable;
        if (typeof variabe == "object")
            throw Error(`BasicIntpError: trying to resolve unknown object '${variable}' with entries ${Object.entries(variable)}`);
        return variable;
    }
    else if (variable.troType === "internal_arrindexing_lazy")
        return eval("variable.troValue.arrFull"+variable.troValue.arrKey);
    else if (literalTypes.includes(variable.troType) || variable.troType.startsWith("internal_"))
        return variable.troValue;
    else if (variable.troType == "lit") {
        var basicVar = bStatus.vars[variable.troValue];
        if (basicVar === undefined) throw lang.refError(undefined, variable.troValue);
        if (basicVar.bvLiteral === "") return "";
        return (basicVar !== undefined) ? basicVar.bvLiteral : undefined;
    }
    else if (variable.troType == "null")
        return undefined;
    // tail error checking
    else
        throw Error("BasicIntpError: unknown variable/object with type "+variable.troType+", with value "+variable.troValue);
}
let curryDefun = function(inputTree, inputValue) {
    let exprTree = cloneObject(inputTree);
    let value = cloneObject(inputValue);
    bF._recurseApplyAST(exprTree, it => {
        if (it.astType == "defun_args") {
            /*if (DBGON) {
                serial.println("[curryDefun] found defun_args #"+it.astValue);
                serial.println(astToString(it));
            }*/
            // apply arg0 into the tree
            if (it.astValue == 0) {
                let valueType = JStoBASICtype(value);
                if (valueType === "usrdefun") {
                    it.astLnum = value.astLnum;
                    it.astLeaves = value.astLeaves;
                    it.astSeps = value.astSeps;
                    it.astValue = value.astValue
                    it.astType = value.astType;
                }
                else {
                    it.astType = valueType
                    it.astValue = value;
                }
                //if (DBGON) serial.println("[curryDefun] applying value "+value);
            }
            // shift down arg index
            else {
                it.astValue -= 1;
                //if (DBGON) serial.println("[curryDefun] decrementing arg index");
            }

            /*if (DBGON) {
                serial.println("[curryDefun] after the task:");
                serial.println(astToString(it));
            }*/
        }
    });

    return exprTree;
}
let argCheckErr = function(lnum, o) {
    if (o === undefined || o.troType == "null") throw lang.refError(lnum, "(variable undefined)");
    if (o.troType == "lit" && bStatus.vars[o.troValue] === undefined) throw lang.refError(lnum, o.troValue);
}
let oneArg = function(lnum, stmtnum, args, action) {
    if (args.length != 1) throw lang.syntaxfehler(lnum, args.length+lang.aG);
    argCheckErr(lnum, args[0]);
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
let _primesgen = function() {
    let primesgen = new ForGen(2,0);
    primesgen.hasNext = (_) => true;
    primesgen.getNext = function(_) {
        do {
            primesgen.current += 1;
        } while (!(function(n){
            if (n == 2 || n == 3) return true;
            if (n % 2 == 0 || n % 3 == 0) return false;
            for (let i = 5; i * i <= n; i = i + 6)
                if (n % i == 0 || n % (i + 2) == 0)
                    return false;
            return true;
        })(primesgen.current));

        return primesgen.current;
    };
    primesgen.toString = (_) => "Generator: primes";
    return primesgen;
}
let _basicConsts = {
   "NIL": new BasicVar([], "array"),
   "PI": new BasicVar(Math.PI, "num"),
   "TAU": new BasicVar(Math.PI * 2.0, "num"),
   "EULER": new BasicVar(Math.E, "num"),
   "PRIMES": new BasicVar(_primesgen, "generator")
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

    this.hasNext = function() {
        return this.current*this.stepsgn + this.step*this.stepsgn <= (this.end + this.step)*this.stepsgn;
        // 1 to 10 step 1
        // 1 + 1 <= 11 -> true
        // 10 + 1 <= 11 -> true
        // 11 + 1 <= 11 -> false

        // 10 to 1 step -1
        // -10 + 1 <= 0 -> true
        // -1 + 1 <= 0 -> true
        // 0 + 1 <= 0 -> false
    }

    // mutableVar: the actual number stored into the FOR-Variable, because BASIC's FOR-Var is mutable af
    // returns undefined if there is no next()
    this.getNext = function(mutated) {
        //if (mutated === undefined) throw "InternalError: parametre is missing";
        if (mutated !== undefined) this.current = (mutated|0);
        this.current += this.step;
        //serial.println(`[BASIC.FORGEN] ${(mutated|0)} -> ${this.current}`);
        return this.hasNext() ? this.current : undefined;
    }

    this.toArray = function() {
        let a = [];
        let cur = this.start;
        while (cur*this.stepsgn + this.step*this.stepsgn <= (this.end + this.step)*this.stepsgn) {
            a.push(cur);
            cur += this.step;
        }
        return a;
    }
    this.reset = function() {
        this.current = this.start;
    }
    this.toString = function() {
        return `Generator: ${this.start} to ${this.end}`+((this.step !== 1) ? ` step ${this.step}` : '');
    }
}
let bStatus = {};
bStatus.gosubStack = [];
bStatus.forLnums = {}; // key: forVar, value: [lnum, stmtnum]
bStatus.forStack = []; // forVars only
bStatus.vars = initBvars(); // contains instances of BasicVars
bStatus.rnd = 0; // stores mantissa (23 bits long) of single precision floating point number
bStatus.getDimSize = function(array, dim) {
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
bStatus.getArrayIndexFun = function(lnum, stmtnum, arrayName, array) {
    if (lnum === undefined || stmtnum === undefined) throw Error(`Line or statement number is undefined: (${lnum},${stmtnum})`);

    return function(lnum, stmtnum, args, seps) {
        if (lnum === undefined || stmtnum === undefined) throw Error(`Line or statement number is undefined: (${lnum},${stmtnum})`);

        // NOTE: BASIC arrays are index in column-major order, which is OPPOSITE of C/JS/etc.
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
                    throw lang.subscrOutOfRng(lnum, `${arrayName}${oldIndexingStr} (${lang.ord(dimcnt)} dim)`, d-INDEX_BASE, bStatus.getDimSize(array, dimcnt-1));

                dimcnt += 1;
            });

            if (TRACEON)
                serial.println("ar indexedValue = "+`/*ar1*/array${indexingstr}`);

            return {arrFull: array, arrName: arrayName, arrKey: indexingstr};
        });
    };
};
bStatus.getDefunThunk = function(lnum, stmtnum, exprTree) {
    if (lnum === undefined || stmtnum === undefined) throw Error(`Line or statement number is undefined: (${lnum},${stmtnum})`);

    let tree = cloneObject(exprTree); // ALWAYS create new tree instance!
    return function(lnum, stmtnum, args, seps) {
        if (lnum === undefined || stmtnum === undefined) throw Error(`Line or statement number is undefined: (${lnum},${stmtnum})`);

        let argsMap = [];
        args.map(it => {
            argCheckErr(lnum, it);
            return resolve(it);
        }).forEach(arg => argsMap.push(arg));

        if (DBGON) {
            serial.println("[BASIC.getDefunThunk.invoke] unthunking: ");
            serial.println(astToString(tree));
            serial.println("[BASIC.getDefunThunk.invoke] thunk args:");
            serial.println(argsMap);
        }

        // perform renaming
        bF._recurseApplyAST(tree, (it) => {
            if ("defun_args" == it.astType) {
                if (DBGON) {
                    serial.println("[BASIC.getDefunThunk.invoke] thunk renaming arg-tree branch:");
                    serial.println(astToString(it));
                }

                let argsIndex = it.astValue;
                let theArg = argsMap[argsIndex]; // instanceof theArg == resolved version of SyntaxTreeReturnObj

                if (theArg !== undefined) { // this "forgiveness" is required to implement currying
                    if (DBGON) {
                        serial.println("[BASIC.getDefunThunk.invoke] thunk renaming-theArg: "+theArg);
                        serial.println(Object.entries(theArg));
                    }

                    it.astValue = theArg;
                    it.astType = JStoBASICtype(theArg);
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

        // evaluate new tree
        return resolve(bF._executeSyntaxTree(lnum, stmtnum, tree, 0));
    }
};
/* Accepts troValue, assignes to BASIC variable, and returns internal_assign_object
 * @params troValue Variable to assign into
 * @params rh the value, resolved
 */
bStatus.addAsBasicVar = function(lnum, troValue, rh) {
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
        let type = JStoBASICtype(rh);
        if (_basicConsts[varname]) throw lang.asgnOnConst(lnum, varname);
        bStatus.vars[varname] = new BasicVar(rh, type);
        return {asgnVarName: varname, asgnValue: rh};
    }
}
bStatus.builtin = {
/*
@param lnum line number
@param args instance of the SyntaxTreeReturnObj

if no args were given (e.g. "10 NEXT()"), args[0] will be: {troType: null, troValue: , troNextLine: 11}
if no arg text were given (e.g. "10 NEXT"), args will have zero length
*/
"=" : {f:function(lnum, stmtnum, args) {
    // THIS FUNCTION MUST BE COPIED TO 'INPUT'
    if (args.length != 2) throw lang.syntaxfehler(lnum, args.length+lang.aG);
    var troValue = args[0].troValue;

    var rh = resolve(args[1]);
    if (rh === undefined) throw lang.refError(lnum, "RH:"+args[1].troValue);

    if (isNumable(rh)) rh = rh*1 // if string we got can be cast to number, do it

    //println(lnum+" = lh: "+Object.entries(args[0]));
    //println(lnum+" = rh raw: "+Object.entries(args[1]));
    //println(lnum+" = rh resolved: "+rh);
    //try { println(lnum+" = rh resolved entries: "+Object.entries(rh)); }
    //catch (_) {}

    return bStatus.addAsBasicVar(lnum, troValue, rh);
}},
"IN" : {f:function(lnum, stmtnum, args) { // almost same as =, but don't actually make new variable. Used by FOR statement
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
"==" : {f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (lh,rh) => lh == rh);
}},
"<>" : {f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (lh,rh) => lh != rh);
}},
"><" : {f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (lh,rh) => lh != rh);
}},
"<=" : {f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh <= rh);
}},
"=<" : {f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh <= rh);
}},
">=" : {f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh >= rh);
}},
"=>" : {f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh >= rh);
}},
"<" : {f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh < rh);
}},
">" : {f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh > rh);
}},
"<<" : {f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh << rh);
}},
">>" : {f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh >>> rh);
}},
"UNARYMINUS" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => -lh);
}},
"UNARYPLUS" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => +lh);
}},
"UNARYLOGICNOT" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => !(lh));
}},
"UNARYBNOT" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => ~(lh));
}},
"BAND" : {f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh & rh);
}},
"BOR" : {f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh | rh);
}},
"BXOR" : {f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh ^ rh);
}},
"!" : {f:function(lnum, stmtnum, args) { // Haskell-style CONS
    return twoArg(lnum, stmtnum, args, (lh,rh) => {
        if (Array.isArray(lh))
            throw lang.illegalType(lnum, lh); // NO ragged array!
        if (!Array.isArray(rh))
            throw lang.illegalType(lnum, rh);
        return [lh].concat(rh);
    });
}},
"~" : {f:function(lnum, stmtnum, args) { // array PUSH
    return twoArg(lnum, stmtnum, args, (lh,rh) => {
        if (!Array.isArray(lh))
            throw lang.illegalType(lnum, lh);
        if (Array.isArray(rh))
            throw lang.illegalType(lnum, rh); // NO ragged array!
        return lh.concat([rh]);
    });
}},
"#" : {f:function(lnum, stmtnum, args) { // array CONCAT
    return twoArg(lnum, stmtnum, args, (lh,rh) => {
        if (!Array.isArray(rh))
            throw lang.illegalType(lnum, rh);
        if (!Array.isArray(lh))
            throw lang.illegalType(lnum, lh);
        return lh.concat(rh);
    });
}},
"+" : {f:function(lnum, stmtnum, args) { // addition, string concat
    return twoArg(lnum, stmtnum, args, (lh,rh) => (!isNaN(lh) && !isNaN(rh)) ? (lh*1 + rh*1) : (lh + rh));
}},
"-" : {f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh - rh);
}},
"*" : {f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => lh * rh);
}},
"/" : {f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => {
        if (rh == 0) throw lang.divByZero;
        return lh / rh;
    });
}},
"\\" : {f:function(lnum, stmtnum, args) { // integer division, rounded towards zero
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => {
        if (rh == 0) throw lang.divByZero;
        return (lh / rh)|0;
    });
}},
"MOD" : {f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => {
        if (rh == 0) throw lang.divByZero;
        return lh % rh;
    });
}},
"^" : {f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (lh,rh) => {
        let r = Math.pow(lh, rh);
        if (isNaN(r)) throw lang.badFunctionCallFormat();
        if (!isFinite(r)) throw lang.divByZero;
        return r;
    });
}},
"TO" : {f:function(lnum, stmtnum, args) {
    return twoArgNum(lnum, stmtnum, args, (from, to) => new ForGen(from, to, 1));
}},
"STEP" : {f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (gen, step) => {
        if (!(gen instanceof ForGen)) throw lang.illegalType(lnum, gen);
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
"PRINT" : {f:function(lnum, stmtnum, args, seps) {
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
"EMIT" : {f:function(lnum, stmtnum, args, seps) {
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
"POKE" : {f:function(lnum, stmtnum, args) {
    twoArgNum(lnum, stmtnum, args, (lh,rh) => sys.poke(lh, rh));
}},
"PEEK" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => sys.peek(lh));
}},
"GOTO" : {f:function(lnum, stmtnum, args) {
    // search from gotoLabels first
    let line = gotoLabels[args[0].troValue];
    // if not found, use resolved variable
    if (line === undefined) line = resolve(args[0]);
    if (line < 0) throw lang.syntaxfehler(lnum, line);

    return new JumpObj(line, 0, lnum, line);
}},
"GOSUB" : {f:function(lnum, stmtnum, args) {
    // search from gotoLabels first
    let line = gotoLabels[args[0].troValue];
    // if not found, use resolved variable
    if (line === undefined) line = resolve(args[0]);
    if (line < 0) throw lang.syntaxfehler(lnum, line);

    bStatus.gosubStack.push([lnum, stmtnum + 1]);
    //println(lnum+" GOSUB into "+lh);
    return new JumpObj(line, 0, lnum, line);
}},
"RETURN" : {f:function(lnum, stmtnum, args) {
    var r = bStatus.gosubStack.pop();
    if (r === undefined) throw lang.nowhereToReturn(lnum);
    //println(lnum+" RETURN to "+r);
    return new JumpObj(r[0], r[1], lnum, r);
}},
"CLEAR" : {f:function(lnum, stmtnum, args) {
    bStatus.vars = initBvars();
}},
"PLOT" : {f:function(lnum, stmtnum, args) {
    threeArgNum(lnum, stmtnum, args, (xpos, ypos, color) => graphics.plotPixel(xpos, ypos, color));
}},
"AND" : {f:function(lnum, stmtnum, args) {
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
"OR" : {f:function(lnum, stmtnum, args) {
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
"RND" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => {
        if (!(args.length > 0 && args[0].troValue === 0))
            bStatus.rnd = Math.random();//(bStatus.rnd * 214013 + 2531011) % 16777216; // GW-BASIC does this
        return bStatus.rnd;
    });
}},
"ROUND" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => Math.round(lh));
}},
"FLOOR" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => Math.floor(lh));
}},
"INT" : {f:function(lnum, stmtnum, args) { // synonymous to FLOOR
    return oneArgNum(lnum, stmtnum, args, (lh) => Math.floor(lh));
}},
"CEIL" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => Math.ceil(lh));
}},
"FIX" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => (lh|0));
}},
"CHR" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => String.fromCharCode(lh));
}},
"TEST" : {f:function(lnum, stmtnum, args) {
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
    bStatus.vars[varname] = new BasicVar(asgnObj.asgnValue[0], JStoBASICtype(asgnObj.asgnValue.shift()));
    // stores entire array (sans head) into temporary storage
    bStatus.vars["for var "+varname] = new BasicVar(asgnObj.asgnValue, "array");
    // put the varname to forstack
    bStatus.forLnums[varname] = [lnum, stmtnum];
    bStatus.forStack.push(varname);
}},
"FOR" : {f:function(lnum, stmtnum, args) { // generator model
    var asgnObj = resolve(args[0]);
    // type check
    if (asgnObj === undefined) throw lang.syntaxfehler(lnum);
    if (!(asgnObj.asgnValue instanceof ForGen)) throw lang.illegalType(lnum, typeof asgnObj);

    var varname = asgnObj.asgnVarName;
    var generator = asgnObj.asgnValue;

    // assign new variable
    // the var itself will have head of the array, and the head itself will be removed from the array
    bStatus.vars[varname] = new BasicVar(generator.start, "num");
    // stores entire array (sans head) into temporary storage
    bStatus.vars["for var "+varname] = new BasicVar(generator, "generator");
    // put the varname to forstack
    bStatus.forLnums[varname] = [lnum, stmtnum];
    bStatus.forStack.push(varname);
}},
"NEXT" : {f:function(lnum, stmtnum, args) {
    // if no args were given
    if (args.length == 0 || (args.length == 1 && args.troType == "null")) {
        // go to most recent FOR
        var forVarname = bStatus.forStack.pop();
        //serial.println(lnum+" NEXT > forVarname = "+forVarname);
        if (forVarname === undefined) {
            throw lang.nextWithoutFor(lnum);
        }

        if (TRACEON) serial.println("[BASIC.FOR] looping "+forVarname);

        var forVar = bStatus.vars["for var "+forVarname].bvLiteral;

        if (forVar instanceof ForGen)
            bStatus.vars[forVarname].bvLiteral = forVar.getNext(bStatus.vars[forVarname].bvLiteral);
        else
            bStatus.vars[forVarname].bvLiteral = forVar.shift();

        if ((bStatus.vars[forVarname].bvLiteral !== undefined)) {
            // feed popped value back, we're not done yet
            bStatus.forStack.push(forVarname);
            let forLnum = bStatus.forLnums[forVarname]
            return new JumpObj(forLnum[0], forLnum[1]+1, lnum, [forLnum[0], forLnum[1]+1]); // goto the statement RIGHT AFTER the FOR-declaration
        }
        else {
            if (forVar instanceof ForGen)
                bStatus.vars[forVarname].bvLiteral = forVar.current; // true BASIC compatibility for generator
            else
                bStatus.vars[forVarname] === undefined; // unregister the variable

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
"INPUT" : {f:function(lnum, stmtnum, args) {
    if (args.length != 1) throw lang.syntaxfehler(lnum, args.length+lang.aG);
    let troValue = args[0].troValue;

    // print out prompt text
    print("? "); var rh = sys.read().trim();

    // if string we got can be cast to number, do it
    // NOTE: empty string will be cast to 0, which corresponds to GW-BASIC
    if (!isNaN(rh)) rh = rh*1

    return bStatus.addAsBasicVar(lnum, troValue, rh);
}},
"CIN" : {f:function(lnum, stmtnum, args) {
    return sys.read().trim();
}},
"END" : {f:function(lnum, stmtnum, args) {
    serial.println("Program terminated in "+lnum);
    return new JumpObj(Number.MAX_SAFE_INTEGER, Number.MAX_SAFE_INTEGER - 1, lnum, undefined); // GOTO far-far-away
}},
"SPC" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (lh) => " ".repeat(lh));
}},
"LEFT" : {f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (str, len) => str.substring(0, len));
}},
"MID" : {f:function(lnum, stmtnum, args) {
    return threeArg(lnum, stmtnum, args, (str, start, len) => str.substring(start-INDEX_BASE, start-INDEX_BASE+len));
}},
"RIGHT" : {f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (str, len) => str.substring(str.length - len, str.length));
}},
"SGN" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => (it > 0) ? 1 : (it < 0) ? -1 : 0);
}},
"ABS" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.abs(it));
}},
"SIN" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.sin(it));
}},
"COS" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.cos(it));
}},
"TAN" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.tan(it));
}},
"EXP" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.exp(it));
}},
"ASN" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.asin(it));
}},
"ACO" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.acos(it));
}},
"ATN" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.atan(it));
}},
"SQR" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.sqrt(it));
}},
"CBR" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.cbrt(it));
}},
"SINH" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.sinh(it));
}},
"COSH" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.cosh(it));
}},
"TANH" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.tanh(it));
}},
"LOG" : {f:function(lnum, stmtnum, args) {
    return oneArgNum(lnum, stmtnum, args, (it) => Math.log(it));
}},
"RESTORE" : {f:function(lnum, stmtnum, args) {
    DATA_CURSOR = 0;
}},
"READ" : {f:function(lnum, stmtnum, args) {
    if (args.length != 1) throw lang.syntaxfehler(lnum, args.length+lang.aG);
    let troValue = args[0].troValue;

    let rh = DATA_CONSTS[DATA_CURSOR++];
    if (rh === undefined) throw lang.outOfData(lnum);

    return bStatus.addAsBasicVar(lnum, troValue, rh);
}},
"DGET" : {f:function(lnum, stmtnum, args) {
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
"MAP" : {f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (fn, functor) => {
        // TODO test only works with DEFUN'd functions
        if (fn.astLeaves === undefined) throw lang.badFunctionCallFormat("Only works with DEFUN'd functions yet");
        if (functor.toArray === undefined && !Array.isArray(functor)) throw lang.syntaxfehler(lnum, functor);
        // generator?
        if (functor.toArray) functor = functor.toArray();

        return functor.map(it => bStatus.getDefunThunk(lnum, stmtnum, fn)(lnum, stmtnum, [it]));
    });
}},
/* Synopsis: FOLD function, init_value, functor
 * a function must accept two arguments, of which first argument will be an accumulator
 */
"FOLD" : {f:function(lnum, stmtnum, args) {
    return threeArg(lnum, stmtnum, args, (fn, init, functor) => {
        // TODO test only works with DEFUN'd functions
        if (fn.astLeaves === undefined) throw lang.badFunctionCallFormat("Only works with DEFUN'd functions yet");
        if (functor.toArray === undefined && !Array.isArray(functor)) throw lang.syntaxfehler(lnum, functor);
        // generator?
        if (functor.toArray) functor = functor.toArray();

        let akku = init;
        functor.forEach(it => {
            akku = bStatus.getDefunThunk(lnum, stmtnum, fn)(lnum, stmtnum, [akku, it]);
        });

        return akku;
    });
}},
/* Syopsis: FILTER function, functor
 */
"FILTER" : {f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (fn, functor) => {
        // TODO test only works with DEFUN'd functions
        if (fn.astLeaves === undefined) throw lang.badFunctionCallFormat("Only works with DEFUN'd functions yet");
        if (functor.toArray === undefined && !Array.isArray(functor)) throw lang.syntaxfehler(lnum, functor);
        // generator?
        if (functor.toArray) functor = functor.toArray();

        return functor.filter(it => bStatus.getDefunThunk(lnum, stmtnum, fn)(lnum, stmtnum, [it]));
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
        throw lang.badFunctionCallFormat(`Not a jump statement: ${jmpFun}`)

    if (jmpTarget === undefined)
        return undefined;

    return bStatus.builtin[jmpFun].f(lnum, stmtnum, [jmpTarget]);
}},
"MIN" : {f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (lh,rh) => (lh > rh) ? rh : lh);
}},
"MAX" : {f:function(lnum, stmtnum, args) {
    return twoArg(lnum, stmtnum, args, (lh,rh) => (lh < rh) ? rh : lh);
}},
"GETKEYSDOWN" : {f:function(lnum, stmtnum, args) {
    let keys = [];
    sys.poke(-40, 255);
    for (let k = -41; k >= -48; k--) {
        keys.push(sys.peek(k));
    }
    return keys;
}},
"~<" : {f:function(lnum, stmtnum, args) { // CURRY operator
    return twoArg(lnum, stmtnum, args, (fn, value) => {
        // TODO test only works with DEFUN'd functions
        if (fn.astLeaves === undefined) throw lang.badFunctionCallFormat("Only works with DEFUN'd functions yet");

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
"TYPEOF" : {f:function(lnum, stmtnum, args) {
    return oneArg(lnum, stmtnum, args, bv => {
        if (bv.Type === undefined || !(bv instanceof BasicVar))
            return JStoBASICtype(bv);
        return bv.bvType;
    });
}},
"LEN" : {f:function(lnum, stmtnum, args) {
    return oneArg(lnum, stmtnum, args, lh => {
        if (lh.length === undefined) throw lang.illegalType();
        return lh.length;
    });
}},
"HEAD" : {f:function(lnum, stmtnum, args) {
    return oneArg(lnum, stmtnum, args, lh => {
        if (lh.length === undefined || lh.length < 1) throw lang.illegalType();
        return lh[0];
    });
}},
"TAIL" : {f:function(lnum, stmtnum, args) {
    return oneArg(lnum, stmtnum, args, lh => {
        if (lh.length === undefined || lh.length < 1) throw lang.illegalType();
        return lh.slice(1, lh.length);
    });
}},
"INIT" : {f:function(lnum, stmtnum, args) {
    return oneArg(lnum, stmtnum, args, lh => {
        if (lh.length === undefined || lh.length < 1) throw lang.illegalType();
        return lh.slice(0, lh.length - 1);
    });
}},
"LAST" : {f:function(lnum, stmtnum, args) {
    return oneArg(lnum, stmtnum, args, lh => {
        if (lh.length === undefined || lh.length < 1) throw lang.illegalType();
        return lh[lh.length - 1];
    });
}},
"CLS" : {f:function(lnum, stmtnum, args) {
    con.clear();
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
"RESOLVE" : {f:function(lnum, stmtnum, args) {
    if (DBGON) {
        return oneArg(lnum, stmtnum, args, (it) => {
            println(it);
        });
    }
    else {
        throw lang.syntaxfehler(lnum);
    }
}},
"RESOLVEVAR" : {f:function(lnum, stmtnum, args) {
    if (DBGON) {
        return oneArg(lnum, stmtnum, args, (it) => {
            let v = bStatus.vars[args[0].troValue];
            if (v === undefined) println("Undefined variable: "+args[0].troValue);
            else println(`type: ${v.bvType}, value: ${v.bvLiteral}`);
        });
    }
    else {
        throw lang.syntaxfehler(lnum);
    }
}},
"UNRESOLVE" : {f:function(lnum, stmtnum, args) {
    if (DBGON) {
        println(args[0]);
    }
    else {
        throw lang.syntaxfehler(lnum);
    }
}},
"UNRESOLVE0" : {f:function(lnum, stmtnum, args) {
    if (DBGON) {
        println(Object.entries(args[0]));
    }
    else {
        throw lang.syntaxfehler(lnum);
    }
}}
};
Object.freeze(bStatus.builtin);
let bF = {};
bF._1os = {"!":1,"~":1,"#":1,"<":1,"=":1,">":1,"*":1,"+":1,"-":1,"/":1,"^":1,":":1,"$":1};
bF._2os = {"<":1,"=":1,">":1,"~":1,"$":1,"*":1};
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
bF._is2o = function(code) {
    return bF._2os[String.fromCharCode(code)]
};
bF._isUnary = function(code) {
    return bF._uos[String.fromCharCode(code)]
}
bF._isParenOpen = function(code) {
    return (code == 0x28 || code == 0x5B);
};
bF._isParenClose = function(code) {
    return (code == 0x29 || code == 0x5D);
};
bF._isParen = function(code) {
    return bF._isParenOpen(code) || bF._isParenClose(code);
};
bF._isSep = function(code) {
    return code == 0x2C || code == 0x3B;
};
// define operator precedence here...
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
    "#": 52, // array concat
    "~<": 100, // curry operator
    "~>": 101, // closure operator
    "=":999,
    "IN":1000
};
bF._opRh = {"^":1,"=":1,"!":1,"IN":1,"~>":1}; // ~< and ~> cannot have same associativity
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
            if (bF._is2o(charCode)) {
                sb += char;
                mode = "o2";
            }
            else if (bF._isUnary(charCode)) {
                tokens.push(sb); sb = "" + char; states.push(mode);
            }
            else if (bF._is1o(charCode)) {
                throw lang.syntaxfehler(lnum, lang.badOperatorFormat);
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
        else if ("o2" == mode) {
            if (bF._is1o(charCode)) {
                throw lang.syntaxfehler(lnum, lang.badOperatorFormat);
            }
            else if (bF._isNum(charCode)) {
                tokens.push(sb); sb = "" + char; states.push("op");
                mode = "num";
            }
            else if (0x22 == charCode) {
                tokens.push(sb); sb = ""; states.push("op");
                mode = "qot";
            }
            else if (" " == char) {
                tokens.push(sb); sb = ""; states.push("op");
                mode = "limbo";
            }
            else if (bF._isParen(charCode)) {
                tokens.push(sb); sb = "" + char; states.push("op");
                mode = "paren"
            }
            else if (bF._isSep(charCode)) {
                tokens.push(sb); sb = "" + char; states.push("op");
                mode = "sep";
            }
            else {
                tokens.push(sb); sb = "" + char; states.push("op");
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
        if (states[k] == "o2") states[k] = "op";
        else if (states[k] == "n2" || states[k] == "nsep") states[k] = "num";
    }

    if (tokens.length != states.length) {
        throw new InternalError("size of tokens and states does not match (line: "+lnum+")\n"+
        tokens+"\n"+states);
    }

    return { "tokens": tokens, "states": states };
};
bF._parserElaboration = function(lnum, tokens, states) {
    var _debugprintElaboration = false;
    if (_debugprintElaboration) println("@@ ELABORATION @@");
    var k = 0;

    // NOTE: malformed numbers (e.g. "_b3", "_", "__") must be re-marked as literal or syntax error

    while (k < states.length) { // using while loop because array size will change during the execution
        if (states[k] == "num" && !reNumber.test(tokens[k]))
            states[k] = "lit";
        else if (states[k] == "lit" && bF._opPrc[tokens[k].toUpperCase()] !== undefined)
            states[k] = "op";
        else if (tokens[k].toUpperCase() == "TRUE" || tokens[k].toUpperCase() == "FALSE")
            states[k] = "bool";
        else if (tokens[k] == ":" && states[k] == "op")
            states[k] = "seq";

        // decimalise hex/bin numbers (because Nashorn does not support binary literal)
        if (states[k] == "num") {
            if (tokens[k].toUpperCase().startsWith("0B")) {
                tokens[k] = parseInt(tokens[k].substring(2, tokens[k].length), 2) + "";
            }
        }


        k += 1;
    }
};
bF._recurseApplyAST = function(tree, action) {
    if (tree.astLeaves === undefined || tree.astLeaves[0] === undefined)
        return action(tree);
    else {
        action(tree);
        tree.astLeaves.forEach(it => bF._recurseApplyAST(it, action))
    }
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
    | "IF" , expr_sans_asgn , "THEN" , expr , ["ELSE" , expr]
    | kywd , expr - "(" (* also deals with FOR statement *)
    (* at this point, if OP is found in paren-level 0, skip function_call *)
    | function_call
    | expr , op , expr
    | op_uni , expr ;

expr_sans_asgn = ? identical to expr except errors out whenever "=" is found ? ;

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
1. funcname
    1. arg0
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
        let treeHead = String.fromCharCode(0x2502,32).repeat(recDepth);
        bF.parserPrintdbg(`${icon}${lnum} ${treeHead}${tokens.join(' ')}`);
        bF.parserPrintdbg(`${icon}${lnum} ${treeHead}${states.join(' ')}`);
    }
}
bF.parserPrintdbgline = function(icon, msg, lnum, recDepth) {
    if (bF.parserDoDebugPrint) {
        let treeHead = String.fromCharCode(0x2502,32).repeat(recDepth);
        bF.parserPrintdbg(`${icon}${lnum} ${treeHead}${msg}`);
    }
}

/**
 * @return ARRAY of BasicAST
 */
bF._parseTokens = function(lnum, tokens, states) {
    bF.parserPrintdbg2('Line ', lnum, tokens, states, 0);

    if (tokens.length !== states.length) throw lang.syntaxfehler(lnum);
    if (tokens[0] == "REM" && states[0] != "qot") return;

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
        bF.parserPrintdbgline('$', 'It was NOT!', lnum, recDepth);
        if (!(e instanceof ParserError)) throw e;
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
    | "IF" , expr_sans_asgn , "THEN" , expr , ["ELSE" , expr]
    | kywd , expr (* also deals with FOR statement; kywd = ? words that exists on the list of predefined function that are not operators ? ; *)
    | function_call
    | expr , op , expr
    | op_uni , expr ;

 * @return: BasicAST
 */
bF._parseExpr = function(lnum, tokens, states, recDepth, ifMode) {
    bF.parserPrintdbg2('E', lnum, tokens, states, recDepth);

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
        bF.parserPrintdbgline('E', 'Literal Call', lnum, recDepth);
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
    //    | "(" , expr , ")"
    if (parenStart == 0 && parenEnd == tokens.length - 1) {
        bF.parserPrintdbgline('E', '( Expr )', lnum, recDepth);

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
        bF.parserPrintdbgline('E', "Trying IF Expression...", lnum, recDepth);
        return bF._parseIfMode(lnum, tokens, states, recDepth + 1, false);
    }
    // if ParserError is raised, continue to apply other rules
    catch (e) {
        bF.parserPrintdbgline('E', 'It was NOT!', lnum, recDepth);
        if (!(e instanceof ParserError)) throw e;
    }

    /*************************************************************************/

    // ## case for:
    //    | kywd , expr (* kywd = ? words that exists on the list of predefined function that are not operators ? ; *)
    if (bStatus.builtin[headTkn] && headSta == "lit" && !bF._opPrc[headTkn] &&
        states[1] != "paren"
    ) {
        bF.parserPrintdbgline('E', 'Builtin Function Call w/o Paren', lnum, recDepth);

        return bF._parseFunctionCall(lnum, tokens, states, recDepth + 1);
    }

    /*************************************************************************/

    // ## case for:
    //    (* at this point, if OP is found in paren-level 0, skip function_call *)
    //    | function_call ;
    if (topmostOp === undefined) { // don't remove this IF statement!
        try {
            bF.parserPrintdbgline('E', "Trying Function Call...", lnum, recDepth);
            return bF._parseFunctionCall(lnum, tokens, states, recDepth + 1);
        }
        // if ParserError is raised, continue to apply other rules
        catch (e) {
            bF.parserPrintdbgline('E', 'It was NOT!', lnum, recDepth);
            if (!(e instanceof ParserError)) throw e;
        }
    }

    /*************************************************************************/

    // ## case for:
    //    | expr , op, expr
    //    | op_uni , expr
    // if operator is found, split by the operator and recursively parse the LH and RH
    if (topmostOp !== undefined) {
        bF.parserPrintdbgline('E', 'Operators', lnum, recDepth);

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
function_call =
      ident , "(" , [expr , {argsep , expr} , [argsep]] , ")"
    | ident , expr , {argsep , expr} , [argsep] ;
 * @return: BasicAST
 */
bF._parseFunctionCall = function(lnum, tokens, states, recDepth) {
    bF.parserPrintdbg2(String.fromCharCode(0x192), lnum, tokens, states, recDepth);

    /*************************************************************************/

    let parenDepth = 0;
    let parenStart = -1;
    let parenEnd = -1;
    let _argsepsOnLevelZero = []; // argseps collected when parenDepth == 0
    let _argsepsOnLevelOne = []; // argseps collected when parenDepth == 1

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

        if (parenDepth == 0 && states[k] == "sep")
            _argsepsOnLevelZero.push(k);
        if (parenDepth == 1 && states[k] == "sep")
            _argsepsOnLevelOne.push(k);
    }

    // unmatched brackets, duh!
    if (parenDepth != 0) throw lang.syntaxfehler(lnum, lang.unmatchedBrackets);
    let parenUsed = (parenStart == 1);
    // && parenEnd == tokens.length - 1);
    // if starting paren is found, just use it
    // this prevents "RND(~~)*K" to be parsed as [RND, (~~)*K]

    /*************************************************************************/

    // ## case for:
    //      ident , "(" , [expr , {argsep , expr} , [argsep]] , ")"
    //    | ident , expr , {argsep , expr} , [argsep] ;
    bF.parserPrintdbgline(String.fromCharCode(0x192), `Function Call (parenUsed: ${parenUsed})`, lnum, recDepth);

    let treeHead = new BasicAST();
    treeHead.astLnum = lnum;

    // set function name and also check for syntax by deliberately parsing the word
    treeHead.astValue = bF._parseIdent(lnum, [tokens[0]], [states[0]], recDepth + 1).astValue; // always UPPERCASE

    // 5 8 11 [end]
    let argSeps = parenUsed ? _argsepsOnLevelOne : _argsepsOnLevelZero; // choose which "sep tray" to use
    bF.parserPrintdbgline(String.fromCharCode(0x192), "argSeps = "+argSeps, lnum, recDepth);
    // 1 6 9 12
    let argStartPos = [1 + (parenUsed)].concat(argSeps.map(k => k+1));
    bF.parserPrintdbgline(String.fromCharCode(0x192), "argStartPos = "+argStartPos, lnum, recDepth);
    // [1,5) [6,8) [9,11) [12,end)
    let argPos = argStartPos.map((s,i) => {return{start:s, end:(argSeps[i] || (parenUsed ? parenEnd : tokens.length) )}}); // use end of token position as separator position
    bF.parserPrintdbgline(String.fromCharCode(0x192), "argPos = "+argPos.map(it=>`${it.start}/${it.end}`), lnum, recDepth);

    // check for trailing separator


    // recursively parse function arguments
    treeHead.astLeaves = argPos.map((x,i) => {
        bF.parserPrintdbgline(String.fromCharCode(0x192), 'Function Arguments #'+(i+1), lnum, recDepth);

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
    bF.parserPrintdbgline(String.fromCharCode(0x192), "astSeps = "+treeHead.astSeps, lnum, recDepth);

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
    bF.parserPrintdbg2(String.fromCharCode(0xA2), lnum, tokens, states, recDepth);

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


// @return is defined in BasicAST
let JStoBASICtype = function(object) {
    if (typeof object === "boolean") return "bool";
    else if (object === undefined) return "null";
    else if (object.arrName !== undefined) return "internal_arrindexing_lazy";
    else if (object.asgnVarName !== undefined) return "internal_assignment_object";
    else if (object instanceof ForGen || object.start !== undefined && object.end !== undefined && typeof object.hasNext == "function") return "generator";
    else if (object instanceof BasicAST || object.astLeaves !== undefined) return "usrdefun";
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
/**
 * @param lnum line number of BASIC
 * @param syntaxTree BasicAST
 * @param recDepth recursion depth used internally
 *
 * @return syntaxTreeReturnObject if recursion is escaped
 */
bF._troNOP = function(lnum, stmtnum) { return new SyntaxTreeReturnObj("null", undefined, [lnum, stmtnum+1]); }
bF._executeSyntaxTree = function(lnum, stmtnum, syntaxTree, recDepth) {
    if (lnum === undefined || stmtnum === undefined) throw Error(`Line or statement number is undefined: (${lnum},${stmtnum})`);

    let _debugExec = (!PROD) && true;
    let _debugPrintCurrentLine = (!PROD) && true;
    let recWedge = ">".repeat(recDepth) + " ";

    if (_debugExec || _debugPrintCurrentLine) serial.println(recWedge+"@@ EXECUTE @@");
    if (_debugPrintCurrentLine && recDepth == 0) {
        serial.println("Syntax Tree in "+lnum+":");
        serial.println(astToString(syntaxTree));
    }

    if (syntaxTree == undefined) return bF._troNOP(lnum, stmtnum);
    else if (syntaxTree.astValue == undefined) { // empty meaningless parens
        if (syntaxTree.astLeaves.length > 1) throw Error("WTF");
        return bF._executeSyntaxTree(lnum, stmtnum, syntaxTree.astLeaves[0], recDepth);
    }
    else if (syntaxTree.astType == "function" || syntaxTree.astType == "op") {
        if (_debugExec) serial.println(recWedge+"function|operator");
        if (_debugExec) serial.println(recWedge+astToString(syntaxTree));
        var funcName = syntaxTree.astValue.toUpperCase();
        var func = (bStatus.builtin[funcName] === undefined) ? undefined : bStatus.builtin[funcName].f;


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
                var iftest = bStatus.builtin["TEST"].f(lnum, stmtnum, [testedval]);

                if (!iftest && syntaxTree.astLeaves[2] !== undefined)
                    return bF._executeSyntaxTree(lnum, stmtnum, syntaxTree.astLeaves[2], recDepth + 1);
                else if (iftest)
                    return bF._executeSyntaxTree(lnum, stmtnum, syntaxTree.astLeaves[1], recDepth + 1);
                else
                    return bF._troNOP(lnum, stmtnum);
            }
            catch (e) {
                serial.printerr(`${e}\n${e.stack || "Stack trace undefined"}`);
                throw lang.errorinline(lnum, "TEST", e);
            }
        }
        else if ("DEFUN" == funcName) {
            if (syntaxTree.astLeaves.length !== 2) throw lang.syntaxfehler(lnum, "DEFUN 1");
            let nameTree = syntaxTree.astLeaves[0];
            let exprTree = syntaxTree.astLeaves[1];

            // create parametres map
            // NOTE: firstmost param ('x' as in foo(x,y,z)) gets index 0
            let defunName = nameTree.astValue.toUpperCase();
            let defunRenamingMap = {};
            nameTree.astLeaves.forEach((it, i) => {
                if (it.astType !== "lit") throw lang.syntaxfehler(lnum, "4");
                return defunRenamingMap[it.astValue] = i;
            });

            // rename the parametres
            bF._recurseApplyAST(exprTree, (it) => {
                if (it.astType == "lit" || it.astType == "function") {
                    // check if parametre name is valid
                    // if the name is invalid, regard it as a global variable (i.e. do nothing)
                    if (defunRenamingMap[it.astValue] !== undefined) {
                        it.astType = "defun_args";
                        it.astValue = defunRenamingMap[it.astValue];
                    }
                }
            });

            // test print new tree
            if (DBGON) {
                serial.println("[BASIC.DEFUN] defun debug info for function "+defunName);
                serial.println("[BASIC.DEFUN] defun name tree: ");
                serial.println(astToString(nameTree));
                serial.println("[BASIC.DEFUN] defun renaming map: "+Object.entries(defunRenamingMap));
                serial.println("[BASIC.DEFUN] defun expression tree:");
                serial.println(astToString(exprTree));
            }
            // check if the variable name already exists
            // search from constants
            if (_basicConsts[defunName]) throw lang.asgnOnConst(lnum, defunName);
            // search from builtin functions
            if (bStatus.builtin[defunName] !== undefined || bF[defunName.toLowerCase()] !== undefined)
                throw lang.dupDef(lnum, stmtnum, defunName);

            // finally assign the function to the variable table
            bStatus.vars[defunName] = new BasicVar(exprTree, "usrdefun");

            return new SyntaxTreeReturnObj("internal_lambda", exprTree, [lnum, stmtnum + 1]);
        }
        else if ("ON" == funcName) {
            if (syntaxTree.astLeaves.length < 3) throw lang.badFunctionCallFormat();

            let testValue = bF._executeSyntaxTree(lnum, stmtnum, syntaxTree.astLeaves[0], recDepth + 1);
            let functionName = syntaxTree.astLeaves[1].astValue;
            let arrays = [];
            for (let k = 2; k < syntaxTree.astLeaves.length; k++)
                arrays.push(bF._executeSyntaxTree(lnum, stmtnum, syntaxTree.astLeaves[k], recDepth + 1));

            try  {
                let r = bStatus.builtin["ON"].f(lnum, stmtnum, [functionName, testValue].concat(arrays))
                return new SyntaxTreeReturnObj(JStoBASICtype(r.jmpReturningValue), r.jmpReturningValue, r.jmpNext);
            }
            catch (e) {
                serial.printerr(`${e}\n${e.stack || "Stack trace undefined"}`);
                throw lang.errorinline(lnum, "ON error", e);
            }
        }
        else {
            var args = syntaxTree.astLeaves.map(it => bF._executeSyntaxTree(lnum, stmtnum, it, recDepth + 1));

            if (_debugExec) {
                serial.println(recWedge+"fn call name: "+funcName);
                serial.println(recWedge+"fn call args: "+(args.map(it => it.troType+" "+it.troValue)).join(", "));
            }

            // func not in builtins (e.g. array access, user-defined function defuns)
            if (func === undefined) {
                var someVar = bStatus.vars[funcName];

                if (DBGON) {
                    serial.println(lnum+" _executeSyntaxTree: "+someVar);
                    if (typeof someVar == "object")
                        serial.println(lnum+" _executeSyntaxTree: "+Object.entries(someVar));
                }

                if (someVar === undefined) {
                    throw lang.syntaxfehler(lnum, funcName + " is undefined");
                }
                else if ("array" == someVar.bvType) {
                    func = bStatus.getArrayIndexFun(lnum, stmtnum, funcName, someVar.bvLiteral);
                }
                else if ("usrdefun" == someVar.bvType) {
                    func = bStatus.getDefunThunk(lnum, stmtnum, someVar.bvLiteral);
                }
                else {
                    throw lang.syntaxfehler(lnum, funcName + " is not a function or an array");
                }
            }
            // call whatever the 'func' has whether it's builtin or we just made shit up right above
            try {
                if (func === undefined) {
                    throw lang.syntaxfehler(lnum, funcName + " is undefined");
                }

                let funcCallResult = func(lnum, stmtnum, args, syntaxTree.astSeps);

                if (funcCallResult instanceof SyntaxTreeReturnObj) return funcCallResult;

                let retVal = (funcCallResult instanceof JumpObj) ? funcCallResult.jmpReturningValue : funcCallResult;

                return new SyntaxTreeReturnObj(
                        JStoBASICtype(retVal),
                        retVal,
                        (funcCallResult instanceof JumpObj) ? funcCallResult.jmpNext : [lnum, stmtnum + 1]
                );
            }
            catch (e) {
                serial.printerr(`${e}\n${e.stack || "Stack trace undefined"}`);
                throw lang.errorinline(lnum, (funcName === undefined) ? "undefined" : funcName, (e === undefined) ? "undefined" : e);
            }
        }
    }
    // array indexing in the tree (caused by indexing array within recursive DEFUN)
    else if (syntaxTree.astType == "array" && syntaxTree.astLeaves[0] !== undefined) {
        let indexer = bStatus.getArrayIndexFun(lnum, stmtnum, "substituted array", syntaxTree.astValue);
        let indices = syntaxTree.astLeaves.map(it=>bF._executeSyntaxTree(lnum, stmtnum, it, recDepth + 1));
        let retVal = indexer(lnum, stmtnum, indices);
        if (_debugExec) serial.println(recWedge+`indexing substituted array(${Object.entries(indices)}) = ${Object.entries(retVal)}`);
        return new SyntaxTreeReturnObj(
                JStoBASICtype(retVal),
                retVal,
                [lnum, stmtnum + 1]
        );
    }
    // userdefun with args
    // apply given arguments (syntaxTree.astLeaves) to the expression tree and evaluate it
    // if tree has leaves:
    else if (syntaxTree.astType == "usrdefun" && syntaxTree.astLeaves[0] !== undefined) {
        let oldTree = syntaxTree.astValue;
        let argsTro = syntaxTree.astLeaves.map(it => bF._executeSyntaxTree(lnum, stmtnum, it, recDepth + 1));
        let newTree = oldTree; // curryDefun() will make a clone of it for us
        for (let k = 0; k < argsTro.length; k++) {
            newTree = curryDefun(oldTree, argsTro[k].troValue);
        }

        // make a javascript function out of the new tree, thess lines are now basically the same as above function calling lines
        let func = bStatus.getDefunThunk(lnum, stmtnum, newTree);

        // call whatever the 'func' has whether it's builtin or we just made shit up right above
        try {
            //let funcCallResult = func(lnum, stmtnum, argsTro, syntaxTree.astSeps);
            let funcCallResult = func(lnum, stmtnum, [], syntaxTree.astSeps);

            if (funcCallResult instanceof SyntaxTreeReturnObj) return funcCallResult;

            let retVal = (funcCallResult instanceof JumpObj) ? funcCallResult.jmpReturningValue : funcCallResult;

            return new SyntaxTreeReturnObj(
                    JStoBASICtype(retVal),
                    retVal,
                    (funcCallResult instanceof JumpObj) ? funcCallResult.jmpNext : [lnum, stmtnum + 1]
            );
        }
        catch (e) {
            serial.printerr(`${e}\n${e.stack || "Stack trace undefined"}`);
            throw lang.errorinline(lnum, (funcName === undefined) ? "undefined" : funcName, (e === undefined) ? "undefined" : e);
        }
    }
    else if (syntaxTree.astType == "num") {
        if (_debugExec) serial.println(recWedge+"num "+((syntaxTree.astValue)*1));
        return new SyntaxTreeReturnObj(syntaxTree.astType, (syntaxTree.astValue)*1, [lnum, stmtnum + 1]);
    }
    else if (syntaxTree.astType == "lit" || literalTypes.includes(syntaxTree.astType)) {
        if (_debugExec) serial.println(recWedge+"literal with astType: "+syntaxTree.astType+", astValue: "+syntaxTree.astValue);
        return new SyntaxTreeReturnObj(syntaxTree.astType, syntaxTree.astValue, [lnum, stmtnum + 1]);
    }
    else if (syntaxTree.astType == "null") {
        if (_debugExec) serial.println(recWedge+"null")
        return bF._executeSyntaxTree(lnum, stmtnum, syntaxTree.astLeaves[0], recDepth + 1);
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
    bF._parserElaboration(lnum, tokens, states);

    // PARSING (SYNTAX ANALYSIS)
    let syntaxTrees = bF._parseTokens(lnum, tokens, states);

    // syntax tree pruning

    // turn UNARYMINUS(num) to -num
    syntaxTrees.forEach(syntaxTree => {
        if (syntaxTree !== undefined) {
            bF._recurseApplyAST(syntaxTree, tree => {
                if (tree.astValue == "UNARYMINUS" && tree.astType == "op" &&
                    tree.astLeaves[1] === undefined && tree.astLeaves[0] !== undefined && tree.astLeaves[0].astType == "num"
                ) {
                    tree.astValue = -(tree.astLeaves[0].astValue);
                    tree.astType = JStoBASICtype(tree.astValue);
                    tree.astLeaves = [];
                }
                else if (tree.astValue == "UNARYPLUS" && tree.astType == "op" &&
                    tree.astLeaves[1] === undefined && tree.astLeaves[0] !== undefined && tree.astLeaves[0].astType == "num"
                ) {
                    tree.astValue = +(tree.astLeaves[0].astValue);
                    tree.astType = JStoBASICtype(tree.astValue);
                    tree.astLeaves = [];
                }
            });
        }
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
    bStatus.vars = initBvars();
    gotoLabels = {};
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
