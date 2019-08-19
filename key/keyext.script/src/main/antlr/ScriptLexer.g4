lexer grammar ScriptLexer;

WS : [ \t\n\r]+ -> channel(HIDDEN) ;

//comments, allowing nesting.
SINGLE_LINE_COMMENT : '//' ~[\r\n]* -> channel(HIDDEN);
MULTI_LINE_COMMENT  : '/*' -> more, pushMode(COMMENT);

CASES: 'cases';
CASE: 'case';
TRY: 'try';
CLOSES: 'closes';
DERIVABLE : 'derivable';
DEFAULT: 'default';
ASSIGN : ':=';
LBRACKET: '[';
RBRACKET:']';
USING : 'using';
MATCH : 'match';
SCRIPT : 'script' ;
TRUE : 'true' ;
FALSE : 'false' ;
CALL : 'call' ;
REPEAT : 'repeat' ;
/*INT : 'int' ;
BOOL: 'bool' ;
TERMTYPE : 'term' ;*/
FOREACH : 'foreach' ;
THEONLY : 'theonly' ;
STRICT : 'strict' ;
RELAX : 'relax';
IF:'if';
WHILE:'while';
INDENT : '{' ;
DEDENT : '}' ;
SEMICOLON : ';' ;
COLON : ':' ;
SUBST_TO: '\\';

STRING_LITERAL_DOUBLE : '"'  -> more, pushMode(STRINGD);
STRING_LITERAL_SINGLE : '\'' -> more, pushMode(STRINGS);
TERM_LITERAL:           '`'  -> more, pushMode(TERM);

PLUS : '+' ;
MINUS : '-' ;
MUL : '*' ;
DIV : '/' ;
EQ : '=' ;
NEQ : '!=' ;
GEQ : '>=' ;
LEQ : '<=' ;
GE : '>' ;
LE : '<' ;
AND : '&' ;
OR: '|' ;
IMP : '==>' ;
EQUIV : '<=>' ;
NOT: 'not';
COMMA: ',';
LPAREN: '(';
RPAREN: ')';
EXE_MARKER: '\u2316' -> channel(HIDDEN);
QUESTION_MARK: '?';
BIND: 'bind';
IN:'in';

DIGITS : DIGIT+ ;
fragment DIGIT : [0-9] ;
ID : ([a-zA-Z]|'#'|'_') ([_a-zA-Z0-9] | '.' | '\\'| '#'|'<'|'>')*;

ERROR_CHAR: .;

mode COMMENT;
END_COMMENT: '*/'-> popMode, type(MULTI_LINE_COMMENT), channel(HIDDEN);
COMMENT_CHAR: . -> more;

mode STRINGD;
STRING_DOUBLE_END : '"' -> type(STRING_LITERAL_DOUBLE), popMode;
STRING_DOUBLE_ANY : .   -> more;

mode STRINGS;
STRING_SINGLE_END : '\'' -> type(STRING_LITERAL_SINGLE), popMode;
STRING_SINGLE_ANY : .   -> more;

mode TERM;
TERM_END : '`' -> type(TERM_LITERAL), popMode;
TERM_ANY : .   -> more;
