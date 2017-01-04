lexer grammar TranslationTacletLexer;

// Rule definition keywords

TACLETS
    : '\\taclets' ;

TRANSLATION
    : '\\translation' ;

CONDITION
    : '\\condition' ;

LOAD
    : '\\load' ;

LOAD_PARAMS
    : '\\load_params' ;

SUPER_CALL
	: '\\superCall' ;

NEGATE
    : '\\negate' ;

STORE
    : '\\store' ;

CHILD
    : '#child-' ;

// Special instructions

NEW_GLOB_LBL
	: '\\newGlobalLabel' ;

GLOB_LBL
	: '\\globalLabel' ;

NAME_FUNC
	: '\\name' ;

// General punctuation

SEMI
	: ';' ;

COLON
	: ':' ;

DOT
	: '.' ;

COMMA
	: ',' ;

SLASH
	: '/' ;

HASH
	: '#';

LPAREN
	: '(' ;

RPAREN
	: ')' ;

LBRACE
	: '{' ;

RBRACE
	: '}' ;

LANGLE
	: '<' ;

RANGLE
	: '>' ;

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

IS_CONSTRUCTOR    : 'isConstructor' ;
IS_FIELD_REF      : 'isFieldReference' ;
IS_RESULT_VAR     : 'isResultVar' ;
IS_SIMPLE_TYPE    : 'isSimpleType' ;
IS_STATIC         : 'isStatic' ;
IS_SUPER_METHOD   : 'isSuperMethod' ;
IS_VOID           : 'isVoid' ;
STR_EQUALS        : 'strEquals' ;

// Arithmetics

MINUS : '-' ;

// Bytecode directives

ALOAD         : 'ALOAD' ;
ARETURN       : 'ARETURN' ;
ASTORE        : 'ASTORE' ;
BIPUSH        : 'BIPUSH' ;
CHECKCAST     : 'CHECKCAST' ;
DUP           : 'DUP' ;
GETFIELD      : 'GETFIELD' ;
GOTO          : 'GOTO' ;
IADD          : 'IADD' ;
ICONST        : 'ICONST' ;
ICONST_D      : 'ICONST_' DIGIT ;
IF_ACMPNE     : 'IF_ACMPNE' ;
IF_ICMPGE     : 'IF_ICMPGE' ;
IF_ICMPLE     : 'IF_ICMPLE' ;
IF_ICMPNE     : 'IF_ICMPNE' ;
IFEQ          : 'IFEQ' ;
IFNE          : 'IFNE' ;
INEG          : 'INEG' ;
INVOKEVIRTUAL : 'INVOKEVIRTUAL' ;
INVOKESTATIC  : 'INVOKESTATIC' ;
INVOKESPECIAL : 'INVOKESPECIAL' ;
IRETURN       : 'IRETURN' ;
ISTORE        : 'ISTORE' ;
ISUB          : 'ISUB' ;
IXOR          : 'IXOR' ;
LDC           : 'LDC' ;
NEW           : 'NEW' ;
PUTFIELD      : 'PUTFIELD' ;
RETURN        : 'RETURN' ;

// Signature elements

INT_SIG  : 'I';
VOID_SIG : 'V';
L        : 'L';

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

fragment LETTER_NO_L
	: 'a' .. 'z'
	| 'A' .. 'K'
	| 'M' .. 'Z'
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

IDENT_L
    : ( L ) ( DIGIT | LETTER | '_' ) *
    ;

// IDENT has to follow the bytecode directives since
// those could also be matched by IDENT otherwise
IDENT
    : ( LETTER ) ( DIGIT | LETTER | '_' ) *
    ;
