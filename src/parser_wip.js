class ParserError extends Error {
    constructor(...args) {
        super(...args);
        Error.captureStackTrace(this, ParserError);
    }
}
var DEFUNS_BUILD_DEFUNS = false;
var DBGON = true;
let lambdaBoundVars = []; // format: [[a,b],[c]] for "[c]~>[a,b]~>expr"
let bF = {};
bF._isParenOpen = function(code) {
    return (code == 0x28 || code == 0x5B) || (code == '(' || code == '[');
};
bF._isParenClose = function(code) {
    return (code == 0x29 || code == 0x5D) || (code == ')' || code == ']');
};
bF._isMatchingParen = function(open, close) {
    return (open == '(' && close == ')' || open == '[' && close == ']');
}
bF.parserPrintdbg = any => serial.println(any);
bF.parserPrintdbg2 = function(icon, lnum, tokens, states, recDepth) {
    let treeHead = "|  ".repeat(recDepth);
    bF.parserPrintdbg(`${icon}${lnum} ${treeHead}${tokens.join(' ')}`);
    bF.parserPrintdbg(`${icon}${lnum} ${treeHead}${states.join(' ')}`);
}
bF.parserPrintdbgline = function(icon, msg, lnum, recDepth) {
    let treeHead = "|  ".repeat(recDepth);
    bF.parserPrintdbg(`${icon}${lnum} ${treeHead}${msg}`);
}
bF._recurseApplyAST = function(tree, action) {
    if (tree.astLeaves === undefined || tree.astLeaves[0] === undefined)
        return action(tree);
    else {
        action(tree);
        tree.astLeaves.forEach(it => bF._recurseApplyAST(it, action))
    }
}
let lang = {};
lang.syntaxfehler = function(line, reason) {
    return Error("Syntax error" + ((line !== undefined) ? (" in "+line) : "") + ((reason !== undefined) ? (": "+reason) : ""));
};
lang.aG = " arguments were given";

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
    if (bStatus.builtin[headTkn] && headSta == "lit" && !bF._opPrc[headTkn] &&
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
 * @return: Array of [recurseIndex, orderlyIndex] where recurseIndex corresponds with the de-bruijn indexing
 */
bF._findDeBruijnIndex = function(varname) {
    let recurseIndex = -1;
    let orderlyIndex = -1;
    for (recurseIndex = 0; recurseIndex < lambdaBoundVars.length; recurseIndex++) {
        orderlyIndex = lambdaBoundVars[recurseIndex].findIndex(it => it == varname);
        if (orderlyIndex != -1)
            return [recurseIndex, orderlyIndex];
    }
    throw new ParserError("Unbound variable: "+varname);
}
/**
 * @return: BasicAST
 */
bF._pruneTree = function(lnum, tree, recDepth) {    
    if (DBGON) {
        serial.println("[Parser.PRUNE] pruning following subtree:");
        serial.println(astToString(tree));
        if (tree.astValue !== undefined && tree.astValue.astValue !== undefined) {
            serial.println("[Parser.PRUNE] unpacking astValue:");
            serial.println(astToString(tree.astValue));
        }
    }
    
    
    // catch all the bound variables for function definition
    if (tree.astType == "op" && tree.astValue == "~>") {
        let nameTree = tree.astLeaves[0];
        let vars = [];
        nameTree.astLeaves.forEach((it, i) => {
            if (it.astType !== "lit") throw new ParserError("Malformed bound variable for function definition; tree:\n"+astToString(nameTree));
            vars.push(it.astValue);
        });
        
        lambdaBoundVars.unshift(vars);
        
        if (DBGON) {
            serial.println("[Parser.PRUNE.~>] added new bound variables: "+Object.entries(lambdaBoundVars));
        }
    }
    
    
    // depth-first run
    if (tree.astLeaves[0] != undefined) {
        tree.astLeaves.forEach(it => bF._pruneTree(lnum, it, recDepth + 1));
    }
    
    
    if (tree.astType == "op" && tree.astValue == "~>") {
        
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
                    it.astValue = bF._findDeBruijnIndex(it.astValue);
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
    
    if (DBGON) {
        serial.println("[Parser.PRUNE] pruned subtree:");
        serial.println(astToString(tree));
        if (tree.astValue !== undefined && tree.astValue.astValue !== undefined) {
            serial.println("[Parser.PRUNE] unpacking astValue:");
            serial.println(astToString(tree.astValue));
        }
        
        serial.println("======================================================\n");
    }
    
    return tree;
}


bF._EquationIllegalTokens = ["IF","THEN","ELSE","DEFUN","ON"];
bF.isSemanticLiteral = function(token, state) {
    return undefined == token || "]" == token || ")" == token ||
            "qot" == state || "num" == state || "bool" == state || "lit" == state;
}


/////// TEST/////////
let astToString = function(ast, depth, isFinalLeaf) {
    let l__ = "| ";
    
    let recDepth = depth || 0;
    if (ast === undefined || ast.astType === undefined) return "";
    let sb = "";
    let marker = ("lit" == ast.astType) ? "i" :
                 ("op" == ast.astType) ? "+" :
                 ("string" == ast.astType) ? "@" :
                 ("num" == ast.astType) ? "$" :
                 ("array" == ast.astType) ? "[" :
                 ("defun_args" === ast.astType) ? "d" : "f";
    sb += l__.repeat(recDepth)+`${marker} ${ast.astLnum}: "${ast.astValue}" (astType:${ast.astType}); leaves: ${ast.astLeaves.length}\n`;    
    for (var k = 0; k < ast.astLeaves.length; k++) {
        sb += astToString(ast.astLeaves[k], recDepth + 1, k == ast.astLeaves.length - 1);
        if (ast.astSeps[k] !== undefined)
            sb += l__.repeat(recDepth)+` sep:${ast.astSeps[k]}\n`;
    }
    sb += l__.repeat(recDepth)+"`"+"-".repeat(22)+'\n';
    return sb;
}
let BasicAST = function() {
    this.astLnum = 0;
    this.astLeaves = [];
    this.astSeps = [];
    this.astValue = undefined;
    this.astType = "null"; // lit, op, string, num, array, function, null, defun_args (! NOT usrdefun !)
}
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
    "<~": 100, // curry operator
    "~>": 101, // closure operator
    "=":999,
    "IN":1000
};
bF._opRh = {"^":1,"=":1,"!":1,"IN":1,"<~":1,"~>":1};
let bStatus = {};
bStatus.builtin = {};
["PRINT","NEXT","SPC","CHR","ROUND","SQR","RND","GOTO","GOSUB","DEFUN","FOR","MAP"].forEach(w=>{ bStatus.builtin[w] = 1 });
let lnum = 10;

// if s<2 then (nop1) else (if s < 9999 then nop2 else nop3)
let tokens1 = ["if","s","<","2","then","(","nop1",")","else","(","if","s","<","9999","then","nop2","else","nop3",")"];
let states1 = ["lit","lit","op","num","lit","paren","lit","paren","lit","paren","lit","lit","op","num","lit","lit","lit","lit","paren"];

// DEFUN HYPOT(X,Y) = SQR(X*X+Y*Y)
let tokens2 = ["defun","HYPOT","(","X",",","Y",")","=","SQR","(","X","*","X","+","Y","*","Y",")"];
let states2 = ["lit","lit","paren","lit","sep","lit","paren","op","lit","paren","lit","op","lit","op","lit","op","lit","paren"];

// DEFUN SINC(X) = SIN(X) / X
let tokens3 = ["DEFUN","SINC","(","X",")","=","SIN","(","X",")","/","X"];
let states3 = ["lit","lit","paren","lit","paren","op","lit","paren","lit","paren","op","lit"];

// PRINT(IF S<2 THEN "111" ELSE IF S<3 THEN "222" ELSE "333")
let tokens4 = ["PRINT","(","IF","S","<","2","THEN","111","ELSE","IF","S","<","3","THEN","222","ELSE","333",")"];
let states4 = ["lit","paren","lit","lit","op","lit","lit","qot","lit","lit","lit","op","lit","lit","qot","lit","qot","paren"];

// ON 6*SQR(X-3) GOTO X+1, X+2, X+3
let tokens5 = ["ON","6","*","SQR","(","X","-","3",")","GOTO","X","+","1",",","X","+","2",",","X","+","3"];
let states5 = ["lit","num","op","lit","paren","lit","op","num","paren","lit","lit","op","num","sep","lit","op","num","sep","lit","op","num"];

// FOR K=10 TO 1 STEP -1
let tokens6 = ["FOR","K","=","10","TO","1","STEP","-","1"];
let states6 = ["lit","lit","op","num","op","num","op","op","num"];

// print(chr(47+round(rnd(1))*45);)
let tokens7 = ["PRINT","(","CHR","(","47","+","ROUND","(","RND","(","1",")",")","*","45",")",";",")"];
let states7 = ["lit","paren","lit","paren","num","op","lit","paren","lit","paren","num","paren","paren","op","num","paren","sep","paren"];

// PRINT 4 - 5 * 9
let tokens8 = ["PRINT","4","-","5","*","9"];
let states8 = ["lit","num","op","num","op","num"];

// NEXT
let tokens9 = ["NEXT"];
let states9 = ["lit"];

// PRINT -3
let tokens10 = ["PRINT","-","3"];
let states10 = ["lit","op","num"];

// PRINT SPC(20-I);
let tokens11 = ["PRINT","SPC","(","20","-","I",")",";"];
let states11 = ["lit","lit","paren","num","op","lit","paren","sep"];

// DEFUN FAC(N)=IF N==0 THEN 1 ELSE N*FAC(N-1)
let tokens12 = ["DEFUN","FAC","(","N",")","=","IF","N","==","0","THEN","1","ELSE","N","*","FAC","(","N","-","1",")"];
let states12 = ["lit","lit","paren","lit","paren","op","lit","lit","op","num","lit","num","lit","lit","op","lit","paren","lit","op","num","paren"];

// K = MAP FAC , 1 TO 10
let tokens13 = ["K","=","MAP","FAC",",","1","TO","10"];
let states13 = ["lit","op","lit","lit","sep","num","op","num"];

// DEFUN FIB(N)=IF N==0 THEN 0 ELSE IF N==1 THEN 1 ELSE FIB(N-1)+FIB(N-2)
let tokens14 = ["DEFUN","FIB","(","N",")","=","IF","N","==","0","THEN","0",
    "ELSE","IF","N","==","1","THEN","1",
    "ELSE","FIB","(","N","-","1",")","+","FIB","(","N","-","2",")"];
let states14 = ["lit","lit","paren","lit","paren","op","lit","lit","op","num","lit","num",
    "lit","lit","lit","op","num","lit","num",
    "lit","lit","paren","lit","op","num","paren","op","lit","paren","lit","op","num","paren"];

// PRINT(MAP FIB, 1 TO 10) is not broken, it's obvious syntax error
// use "PRINT MAP(FIB, 1 TO 10)" instead
let tokens15 = ["PRINT","MAP","(","FIB",",","1","TO","10",")"];
let states15 = ["lit","lit","paren","lit","sep","num","op","num","paren"];

// DEFUN KA(X)=IF X>2 THEN DO(PRINT(HAI);PRINT(X)) ELSE DO(PRINT(BYE);PRINT(X))
let tokens16 = ["DEFUN","KA","(","X",")","=","IF","X",">","2","THEN","DO","(","PRINT","(","HAI",")",";","PRINT","(","X",")",")","ELSE","DO","(","PRINT","(","BYE",")",";","PRINT","(","X",")",")"];
let states16 = ["lit","lit","paren","lit","paren","op","lit","lit","op","num","lit","lit","paren","lit","paren","qot","paren","sep","lit","paren","lit","paren","paren","lit","lit","paren","lit","paren","qot","paren","sep","lit","paren","lit","paren","paren"];

// FILTER(FN<~HEAD XS, TAIL XS)
let tokens17 = ["FILTER","(","FN","<~","HEAD","XS",",","TAIL","XS",")"];
let states17 = ["lit","paren","lit","op","lit","lit","sep","lit","lit","paren"];

// K=[X,Y]~>(X+Y)/2
let tokens18 = ["K","=","[","X",",","Y","]","~>","(","X","+","Y",")","/","2"];
let states18 = ["lit","op","paren","lit","sep","lit","paren","op","paren","lit","op","lit","paren","op","num"]

// [A,B]~>[X]~>(X+A)/2
let tokens19 = ["K","=","[","A",",","B","]","~>","[","X","]","~>","(","X","+","A",")","/","2"];
let states19 = ["lit","op","paren","lit","sep","lit","paren","op","paren","lit","paren","op","paren","lit","op","lit","paren","op","num"];

// [A,B]~>MAP([C]~>C<B,A)
let tokens20 = ["[","A",",","B","]","~>","MAP","(","[","C","]","~>","C","<","B",",","A",")"];
let states20 = ["paren","lit","sep","lit","paren","op","lit","paren","paren","lit","paren","op","lit","op","lit","sep","lit","paren"];

// [X]~>FOO([Y]~>[K,X]~>X+K*Y,ZIP(X))
let tokens21 = ["[","X","]","~>","FOO","(","[","Y","]","~>","[","K",",","X","]","~>","X","+","K","*","Y",",","ZIP","(","X",")",")"];
let states21 = ["paren","lit","paren","op","lit","paren","paren","lit","paren","op","paren","lit","sep","lit","paren","op","lit","op","lit","op","lit","sep","lit","paren","lit","paren","paren"];

try  {
    let rawTrees = bF._parseTokens(lnum,
        tokens21,
        states21
    );
    let trees = rawTrees.map(it => bF._pruneTree(lnum, it, 0));
    trees.forEach((t,i) => {
        serial.println("\nParsed Statement #"+(i+1));
        serial.println(astToString(t));
    });
}
catch (e) {
    serial.printerr(e);
    serial.printerr(e.stack || "stack trace undefined");
}
