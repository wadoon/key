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
        simple_expression
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
        load_instr
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
        RETURN
    ;

unary_bytecode_instr
    :
        (
            GOTO
        |
            ICONST
        |
            IF_ICMPLE
        |
            IFEQ
        |
            IFNE
        |
            ISTORE
        )
        
        (
            LOC_REF
        |
            LABEL
        )
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

child_call
    :
        CHILD NUMBER
    ;

// Condition expressions
simple_expression
    :
        meta_var
        comparator
        NUMBER
    ;

meta_var
    :
        NUM_CHILDREN
    ;

comparator
    :
        EQ | LT | LEQ | GT | GEQ
    ;