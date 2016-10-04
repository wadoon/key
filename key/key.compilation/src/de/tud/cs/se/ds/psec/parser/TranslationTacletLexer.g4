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

NEGATE
    : '\\negate';

IF
    : '\\if';

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

// Arithmetics

MINUS : '-' ;

// Bytecode directives

BIPUSH    : 'BIPUSH';
GOTO      : 'GOTO';
IADD      : 'IADD';
ICONST    : 'ICONST';
ICONST_D  : 'ICONST_' DIGIT;
IF_ICMPGE : 'IF_ICMPGE';
IF_ICMPLE : 'IF_ICMPLE';
IF_ICMPNE : 'IF_ICMPNE';
IFEQ      : 'IFEQ';
IFNE      : 'IFNE';
IRETURN   : 'IRETURN';
ISTORE    : 'ISTORE';
ISUB      : 'ISUB';
IXOR      : 'IXOR';
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
