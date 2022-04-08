lexer grammar CASLLexer;

channels {
    C_ANNOTATION_LINE, C_ANNOTATION_INLINE, C_KEY_ANNOTATION
}

/* reserved keywords */
AND: 'and';
ARCH: 'arch';
AS: 'as';
AXIOM: 'axiom';
AXIOMS: 'axioms';
CLOSED: 'closed';
DEF: 'def';
ELSE: 'else';
END: 'end';
EXISTS: 'exists';
FALSE: 'false';
FIT: 'fit';
FORALL: 'forall';
FREE: 'free';
FROM: 'from' -> mode(LIBRARY_MODE);
GENERATED: 'generated';
GIVEN: 'given';
HIDE: 'hide';
IF: 'if';
IN: 'in';
LAMBDA: 'lambda';
LIBRARY: 'library' -> mode(LIBRARY_MODE);
LOCAL: 'local';
NOT: 'not';
OP: 'op';
OPS: 'ops';
PRED: 'pred';
PREDS: 'preds';
RESULT: 'result';
REVEAL: 'reveal';
SORT: 'sort';
SORTS: 'sorts';
SPEC: 'spec';
THEN: 'then';
TO: 'to';
TRUE: 'true';
TYPE: 'type';
TYPES: 'types';
UNIT: 'unit';
UNITS: 'units';
VAR: 'var';
VARS: 'vars';
VERSION: 'version' -> mode(VERSION_MODE);
VIEW: 'view';
WHEN: 'when';
WITH: 'with';
WITHIN: 'within';

/* reserved operators */
COLON: ':';
COLONQ: ':?';
CCEQ: '::=';
EQ: '=';
IMPL: '=>';
EQL: '<=>';
DOT: '.';
BAR: '|';
AMAP: '|->';
DISJ: '\\/';
CONJ: '/\\';

/* brackets */
O_PARENTHESES: '(';
C_PARENTHESES: ')';
O_BRACKET: '[';
C_BRACKET: ']';
O_BRACE: '{';
C_BRACE: '}';

SEMICOLON: ';';
COMMA: ',';
QUESTIONP: '?';
STAR: '*';
RARROW: '->';
EEQUAL: '=e=';
EXISTSB: 'exists!';
//EXP: 'E';
PLACE: '__';
SMALLREL: '<';

// signs
PLUS: '+';
MINUS: '-';
SLASH: '/';
BSLASH: '\\';
AMPERSAND: '&';
BIGREL: '>';
EXCLM: '!';
DOLLAR: '$';
AT: '@';
SHARP: '#';
CARET: '^';
TILDE: '~';

// remove later
ASSOC: 'assoc';
COMM: 'comm';
IDEM: 'idem';


DIGITS
    : DIGIT DIGIT+
    ;

DIGIT
    : [0-9]
    ;

WORDS
    : LETTER WORD? ('_' WORD)*
    ;

DOT_WORDS
    : '.' WORDS
    ;

fragment WORD
    : WORD_CHAR+
    ;

fragment WORD_CHAR
    : LETTER
    | '\''
    | DIGIT
    ;

LETTER
    : [A-Za-z]
    ;


QUOTED_CHAR
    : '\'' CHAR '\''
    ;

STRING
    : '"' CHAR* '"'
    ;

fragment CHAR
    : LETTER | DIGIT
    | '+' | '-' | '*' | '/' | '\\\\' | '&' | '=' | '<' | '>'
    | '!' | '?' | ':' | '.' | '$' | '@' | '#' | '^' | '~'
    | '|'
    | ';' | ',' | '\\\'' | '%' | '_' | ' '
    | '(' | ')' | '[' | ']' | '{' | '}'
    | '\\n' | '\\t' | '\\r' | '\\v' | '\\b' | '\\f'
    | '\\a' | '\\?' | '\\"' | '`'
    | [\p{Blk=Latin_1_Sup}]
    | '\\' DIGIT DIGIT DIGIT
    | '\\x' HEX_CHAR HEX_CHAR
    | '\\o' DIGIT DIGIT DIGIT
    ;

FRACTION
    : NUMBER '.' NUMBER
    ;

FLOATING
    : NUMBER 'E' OPT_SIGN NUMBER
    | FRACTION 'E' OPT_SIGN NUMBER
    ;

fragment OPT_SIGN
    : '+'
    | '-'
    |
    ;

WS
    : [ \t] -> skip
    ;

NL
    : '\r'? '\n' -> skip
    ;

COMMENT
    : '%%' .*? NL -> skip
    ;

COMMENT_MULTILINE
    : '%' ('{' | '[') .*? ('}' | ']') '%' -> skip
    ;

KEY_ANNOTATION
    : '%key(' .*? ')%' -> channel(C_KEY_ANNOTATION)
    ;

ANNOTATION_INLINE
    : '%' [a-z]* '(' .*? ')%' -> channel(C_ANNOTATION_INLINE)
    ;

ANNOTATION_LINE
    : '%' (~[{[(%])? .*? -> channel(C_ANNOTATION_LINE)
    ;

mode LIBRARY_MODE;

fragment PATH_CHAR
    : [A-Za-z0-9]
    | '$' | '-' | '_' | '@' | '.' | '&' | '+' | '!' | '*'
    | '"' | '\'' | '(' | ')' | ',' | ':' | '~'
    | '%' HEX_CHAR HEX_CHAR
    ;

fragment HEX_CHAR
    : [A-Fa-f0-9]
    ;

fragment PATH_WORD
    : PATH_CHAR+
    ;

GET: 'get';

PATH
    : PATH_WORD ('/' PATH_WORD)* -> mode(DEFAULT_MODE)
    ;

URL
    : ('http://' | 'ftp://' | 'file://' ) PATH
    ;

WS_LIB
    : [ \t] -> skip
    ;

NL_LIB
    : '\r'? '\n' -> skip
    ;

COMMENT_LIB
    : '%%' .*? NL -> skip
    ;

COMMENT_MULTILINE_LIB
    : '%{' .*? '}%' -> skip
    ;

ANNOTATION_INLINE_LIB
    : '%(' .*? ')%' -> channel(C_ANNOTATION_INLINE)
    ;

ANNOTATION_LINE_LIB
    : '%' ~[(%] .*? NL -> channel(C_ANNOTATION_LINE)
    ;

mode VERSION_MODE;

fragment NUMBER
    : DIGIT
    | DIGITS
    ;

VERSION_NUM
    : NUMBER ('.' NUMBER)* -> mode(DEFAULT_MODE)
    ;

WS_VERSION
    : [ \t] -> skip
    ;

NL_VERSION
    : '\r'? '\n' -> skip
    ;

COMMENT_VERSION
    : '%%' .*? NL -> skip
    ;

COMMENT_MULTILINE_VERSION
    : '%{' .*? '}%' -> skip
    ;

ANNOTATION_INLINE_VERSION
    : '%(' .*? ')%' -> channel(C_ANNOTATION_INLINE)
    ;

ANNOTATION_LINE_VERSION
    : '%' ~[(%] .*? NL -> channel(C_ANNOTATION_LINE)
    ;
