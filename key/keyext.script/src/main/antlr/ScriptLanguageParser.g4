parser grammar ScriptLanguageParser;

options { tokenVocab=ScriptLexer; }


start
    :  stmtList (script)*
    ;

script
    : SCRIPT name=ID LPAREN signature=argList? RPAREN INDENT body=stmtList DEDENT
    ;


argList
    :   varDecl (COMMA varDecl)*
    ;

varDecl
    :   name=ID COLON type=ID
    ;

stmtList
    :   statement*
    ;


statement
    :   //scriptDecl
      assignment
    | casesStmt
    | scriptCommand
    | unconditionalBlock
    | conditionalBlock
    | letStmt
  //  |   callStmt
    ;

letStmt
    :
        BIND expression
        ( SEMICOLON
        | IN ( statement | INDENT stmtList DEDENT)
        )
    ;

/*scriptDecl
    :
    SCRIPT name=ID '(' signature=argList? ')' INDENT body=stmtList DEDENT
    ;
*/
assignment
    :   variable=ID COLON type=ID SEMICOLON
    |   variable=ID (COLON type=ID)? ASSIGN expression SEMICOLON
    ;


expression
    :
      expression MUL expression #exprMultiplication
    | <assoc=right> expression DIV expression #exprDivision
    | expression op=(PLUS|MINUS) expression #exprLineOperators
    | expression op=(LE|GE|LEQ|GEQ) expression #exprComparison
    | expression op=(NEQ|EQ) expression  #exprEquality
    | expression AND expression   #exprAnd
    | expression OR expression    #exprOr
    | expression IMP expression   #exprIMP
    //|   expression EQUIV expression already covered by EQ/NEQ
    | expression LBRACKET substExpressionList RBRACKET #exprSubst
    | ID LPAREN  (expression (COMMA expression)*)? RPAREN  #function
    | MINUS expression         #exprNegate
    | NOT expression           #exprNot
    | LPAREN expression RPAREN #exprParen
    | literals                 #exprLiterals
    | matchPattern             #exprMatch
;


substExpressionList
    :
    (scriptVar SUBST_TO expression
        (COMMA scriptVar SUBST_TO expression)*
    )?
    ;

literals :
        ID             #literalID
    |   DIGITS         #literalDigits
    |   TERM_LITERAL   #literalTerm
    |   STRING_LITERAL #literalString
    |   TRUE           #literalTrue
    |   FALSE          #literalFalse
;

/**
 * Example: <pre>
    match `f(x) ==>` using [x:term]

     </pre>*/
matchPattern
    :
       MATCH (
         derivable=DERIVABLE derivableExpression=expression
       | (pattern=expression (USING LBRACKET argList RBRACKET)?)
       )
    ;

scriptVar
    :   QUESTION_MARK ID
    ;


casesStmt
    :   CASES INDENT
            casesList*
        (DEFAULT  COLON? INDENT?
            defList=stmtList
          DEDENT?)?
        DEDENT
    ;

casesList
    :    (TRY |
            (CASE  (expression
                | (CLOSES  INDENT closesGuard=stmtList DEDENT) ) ) )
                COLON INDENT? body=stmtList DEDENT?
    ;

/*closesExpression
    : CLOSES  INDENT closesGuard=stmtList DEDENT
    ;*/

unconditionalBlock
    : (kind+=(FOREACH|THEONLY|STRICT|RELAX|REPEAT))+ INDENT stmtList DEDENT
    ;

conditionalBlock
    : kind=(IF|WHILE) LPAREN expression RPAREN INDENT stmtList DEDENT
    ;


scriptCommand
    :   cmd=ID parameters? SEMICOLON
    ;

parameters: parameter+;
parameter :  ((pname=ID EQ)? expr=expression);

/*
callStmt
    :   CALL scriptCommand SEMICOLON
    ;
*/
