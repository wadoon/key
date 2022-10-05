grammar Testgrammar;

@header {
    package antlr;
}

WHILE:
    'while'
    ;

IF:
    'if'
    ;

TRUE:
    'true'
    ;

FALSE:
    'false'
    ;

AND:
    '&&'
    ;

OR:
    '||'
    ;

NUMBER:
    ('0'..'9')+
    ;

EQUALS:
    '='
    ;

VARIABLE:
    ('a'..'z')+
    ;

LBRACKET:
    '{'
    ;

RBRACKET:
    '}'
    ;

LPAREN:
    '('
    ;

RPAREN:
    ')'
    ;

WS:
    (' '|'\r'|'\t'|'\n') -> channel(HIDDEN)
    ;

boolean_expr:
    TRUE | FALSE | VARIABLE EQUALS EQUALS value | boolean_expr AND boolean_expr | boolean_expr OR boolean_expr
    ;

value:
    NUMBER |
    boolean_expr
    ;

assignment:
    VARIABLE EQUALS value
    ;

if_cond:
    IF LPAREN boolean_expr RPAREN LBRACKET statement* RBRACKET
    ;

while_loop:
    WHILE LPAREN boolean_expr RPAREN LBRACKET statement* RBRACKET
    ;

statement:
    assignment | if_cond | while_loop
    ;

program:
    statement+
    ;