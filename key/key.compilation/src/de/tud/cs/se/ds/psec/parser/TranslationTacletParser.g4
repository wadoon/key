parser grammar TranslationTacletParser;

options {
    tokenVocab = TranslationTacletLexer ;
}

definitions
    :
		definition +
        EOF
    ;

definition
    :
        IDENT
        LBRACE
            taclets_reference
            condition *
            translation
        RBRACE
    ;

taclets_reference
    :
        TACLETS
        LPAREN
            STRING_LITERAL
            (COMMA STRING_LITERAL) *
        RPAREN
    ;

condition
    :
        CONDITION
        LPAREN
        expression_atom
        RPAREN
    ;

translation
    :
        TRANSLATION
        LPAREN
            instruction +
        RPAREN
    ;

instruction
    :
        bytecode_instr
    |
        labeled_bytecode_instr
    ;

labeled_bytecode_instr
    :
        LABEL COLON bytecode_instr
    ;

bytecode_instr
    :
        nullary_bytecode_instr
    |
        unary_bytecode_instr
    |
    	putfield_instr
    |
        load_instr
    |
    	method_call
    |
        child_call
    ;

nullary_bytecode_instr
    :
        IADD
    |
        ICONST_D
    |
        IRETURN
    |
        ISUB
    |
        IXOR
    |
        RETURN
    ;

unary_bytecode_instr
    :
        loc_var_unary_instrs LOC_REF   # locVarUnaryBytecodeInstr
    |
    	label_unary_instrs LABEL       # labelUnaryBytecodeInstr
    |
    	int_const_unary_instrs integer # intUnaryBytecodeInstr
    ;

putfield_instr
	:
		PUTFIELD
		(object = LOC_REF)
		DOT
		(field = LOC_REF)
	;

loc_var_unary_instrs
	:
		ALOAD
	|
		ISTORE
	;

label_unary_instrs
	:
		GOTO
	|
		IF_ACMPNE
	|
		IF_ICMPGE
	|
		IF_ICMPLE
	|
		IF_ICMPNE
	|
		IFEQ
	|
		IFNE
	;

int_const_unary_instrs
	:
		BIPUSH
	;

load_instr
    :
        simple_load_instr
    |
        negated_load_instr
    ;

simple_load_instr
    :
        LOAD
        LPAREN
            LOC_REF
        RPAREN
    ;

negated_load_instr
    :
        LOAD
        LPAREN
            NEGATE
            LPAREN
                LOC_REF
            RPAREN
        RPAREN
    ;

method_call
	:
		METHOD_CALL
		LPAREN
			(call = LOC_REF)
		RPAREN
	;

child_call
    :
        CHILD NUMBER
    ;

integer
	:
		MINUS ? NUMBER
	;

// Condition expressions
expression_atom
	:
		NOT ? simple_arithmetic_expression # arithmeticExpressionAtom
	|
		NOT ? special_expression           # specialExpressionAtom
	;

special_expression
	:
		IS_SIMPLE_TYPE
		LPAREN
			LOC_REF
		RPAREN          # simpleTypeExpression
	;

simple_arithmetic_expression
    :
        meta_var
        comparator
        integer
    ;

meta_var
    :
        NUM_CHILDREN
    ;

comparator
    :
        EQ | LT | LEQ | GT | GEQ
    ;
