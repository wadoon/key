lexer grammar TranslationTacletLexer;

// Rule definition keywords

TACLETS
    : '\\taclets' ;

TRANSLATION
    : '\\translation' ;

CONDITION
    : '\\condition' ;

LOAD
    : '\\load';

LOAD_PARAMS
    : '\\load_params';

METHOD_CALL
	: '\\methodCall';

NEGATE
    : '\\negate';

STORE
    : '\\store';

CHILD
    : '#child-'
    ;

// General punctuation

SEMI
	: ';' ;

COLON
	: ':' ;

DOT
	: '.' ;

COMMA
	: ',' ;

LPAREN
	: '(' ;

RPAREN
	: ')' ;

LBRACE
	: '{' ;

RBRACE
	: '}' ;

QUOT
    : '"' ;

// Whitespace, Comments

WS
	: (' '
  |   '\t'
  |   '\n'
  |   '\r' )
  -> channel(HIDDEN) ;

SL_COMMENT
	: '//' (~('\n' | '\uFFFF'))* ('\n' | '\uFFFF' | EOF)
      -> skip //channel(HIDDEN)
    ;

ML_COMMENT
	: '/*' .*? '*/'
	  -> skip //channel(HIDDEN)
    ;

// Expression operators

LT  : '<' ;
GT  : '>' ;
GEQ : '>=' ;
LEQ : '<=' ;
EQ  : '==' ;

AND : '&';
OR  : '|';
NOT : '!';

IS_SIMPLE_TYPE : 'isSimpleType';
IS_RESULT_VAR : 'isResultVar';
IS_CONSTRUCTOR : 'isConstructor';
IS_STATIC : 'isStatic';
IS_VOID : 'isVoid';

// Arithmetics

MINUS : '-' ;

// Bytecode directives

ALOAD     : 'ALOAD';
ARETURN   : 'ARETURN';
ASTORE    : 'ASTORE';
BIPUSH    : 'BIPUSH';
CHECKCAST : 'CHECKCAST';
GETFIELD  : 'GETFIELD';
GOTO      : 'GOTO';
IADD      : 'IADD';
ICONST    : 'ICONST';
ICONST_D  : 'ICONST_' DIGIT;
IF_ACMPNE : 'IF_ACMPNE';
IF_ICMPGE : 'IF_ICMPGE';
IF_ICMPLE : 'IF_ICMPLE';
IF_ICMPNE : 'IF_ICMPNE';
IFEQ      : 'IFEQ';
IFNE      : 'IFNE';
IRETURN   : 'IRETURN';
ISTORE    : 'ISTORE';
ISUB      : 'ISUB';
IXOR      : 'IXOR';
PUTFIELD  : 'PUTFIELD';
RETURN    : 'RETURN';

// Meta variables

NUM_CHILDREN
    : '#num-children'
    ;

// Digit and String tokens, etc.

fragment DIGIT
    : '0'..'9' ;

fragment LETTER
    : 'a'..'z'
    | 'A'..'Z'
    ;

NUMBER
    : DIGIT +
    ;

STRING_LITERAL
	: '"' ('\\' . | ~( '"' | '\\') )* '"' ;

LABEL
    : 'l' DIGIT +
    ;

LOC_REF
    : '#' (LETTER | DIGIT) +
    ;

// IDENT has to follow the bytecode directives since
// those could also be matched by IDENT otherwise
IDENT
    : ( LETTER ) ( DIGIT | LETTER | '_' ) *
    ;
