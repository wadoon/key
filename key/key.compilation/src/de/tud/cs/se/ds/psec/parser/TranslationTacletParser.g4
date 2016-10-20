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
        (name = IDENT)
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
        invoke_instr
    |
    	nullary_bytecode_instr
    |
        unary_bytecode_instr
    |
    	field_instr
    |
        load_instr
    |
    	super_call
    |
    	store_instr
    |
        child_call
    ;

nullary_bytecode_instr
    :
    	ARETURN
    |
    	DUP
    |
        IADD
    |
        ICONST_D
    |
    	INEG
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
        loc_var_unary_instrs (LOC_REF | integer)   # locVarUnaryBytecodeInstr
    |
    	label_unary_instrs LABEL                   # labelUnaryBytecodeInstr
    |
    	int_const_unary_instrs integer             # intUnaryBytecodeInstr
    |
    	string_lit_unary_instrs LOC_REF            # stringLitUnaryBytecodeInstr
    |
    	special_unary_instrs (LOC_REF | type_spec) # specialUnaryInstrs
    ;

field_instr
	:
		(instr = (GETFIELD | PUTFIELD))
		(field = LOC_REF)
	;

loc_var_unary_instrs
	:
		ALOAD
	|
		ASTORE
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

string_lit_unary_instrs
	:
		LDC
	;

special_unary_instrs
	:
		CHECKCAST
	|
		NEW
	;

load_instr
    :
        simple_load_instr
    |
        negated_load_instr
    |
    	params_load_instr
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

params_load_instr
	:
		LOAD_PARAMS
		LPAREN
			LOC_REF
		RPAREN
	;

store_instr
	:
		STORE
		LPAREN
			LOC_REF
		RPAREN
	;

invoke_instr
	:
		invoke_instr_literal
	|
		invoke_instr_sv
	;

invoke_instr_literal
	:
		invoke_op
		method_descriptor
	;

invoke_instr_sv
	:
		invoke_op
		LOC_REF
	;

invoke_op
	:
		INVOKESPECIAL
	|
		INVOKESTATIC
	|
		INVOKEVIRTUAL
	;

super_call
	:
		SUPER_CALL
		LPAREN
			(mname = LOC_REF)
			COMMA
			(elist = LOC_REF)
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

// Typ and Method signatures

// java/lang/String.valueOf(I)Ljava/lang/String;

method_descriptor
	:
		(typename = type_spec)
		DOT
		(mname = method_name)
		(sig = method_sig)
	;

method_name
	:
		IDENT
	|
		LANGLE IDENT RANGLE
	;

method_sig
	:
		LPAREN
			signature_element *
		RPAREN
		method_result_type
	;

method_result_type
	:
		VOID_SIG
	|
		signature_element
	;

signature_element
	:
		primitive_sig_element
	|
		type_sig_element
	;

primitive_sig_element
	:
		INT_SIG
	;

type_sig_element
	:
		IDENT_L
		(
			SLASH
			IDENT
		)*
		SEMI
	;

type_spec
	:
		IDENT
		(
			SLASH
			IDENT
		)*
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
		IS_CONSTRUCTOR
		LPAREN
			LOC_REF
		RPAREN          # isConstructorExpression
	|
		IS_FIELD_REF
		LPAREN
			LOC_REF
		RPAREN          # isFieldReference
	|
		IS_RESULT_VAR
		LPAREN
			LOC_REF
		RPAREN          # isResultVarExpression
	|
		IS_SIMPLE_TYPE
		LPAREN
			LOC_REF
		RPAREN          # simpleTypeExpression
	|
		IS_STATIC
		LPAREN
			LOC_REF
		RPAREN          # isStaticExpression
	|
		IS_SUPER_METHOD
		LPAREN
			(called_method = LOC_REF)
			COMMA
			(compiled_method = LOC_REF)
		RPAREN          # isSuperMethod
	|
		IS_VOID
		LPAREN
			LOC_REF
		RPAREN          # isVoidExpression
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
