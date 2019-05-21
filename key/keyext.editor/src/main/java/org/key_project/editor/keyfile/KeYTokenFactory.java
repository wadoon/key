package org.key_project.editor.keyfile;

import de.uka.ilkd.key.parser.KeYLexer;
import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.Lexer;
import org.fife.ui.rsyntaxtextarea.TokenTypes;

import static de.uka.ilkd.key.parser.KeYLexer.*;

public class KeYTokenFactory extends AntlrTokenMakerFactory implements TokenTypes {
    @Override
    protected int rewriteTokenType(int antlrType) {
        //TODO Map the types
        switch (antlrType) {
            case ABSTRACT:
            case ADD:
            case ADDPROGVARS:
            case ADDRULES:
            case AND:
            case ANTECEDENTPOLARITY:
            case APPLY_UPDATE_ON_RIGID:
            case ASSIGN:
            case ASSUMES:
            case AT:
            case AVOID:
            case AXIOMS:
            case BACKSLASH:
            case BIGINT:
            case BOOTCLASSPATH:
            case CHAR_LITERAL:
            case CHOOSECONTRACT:
            case CLASSPATH:
            case CLOSEGOAL:
            case COLON:
            case COMMA:
            case CONTAINERTYPE:
            case CONTAINS_ASSIGNMENT:
            case CONTRACTS:
            case DEPENDINGON:
            case DIFFERENT:
            case DIFFERENTFIELDS:
            case DIGIT:
            case DIGIT_DISPATCH:
            case DISJOINTMODULONULL:
            case DISPLAYNAME:
            case DOT:
            case DOTRANGE:
            case DOUBLECOLON:
            case DROP_EFFECTLESS_ELEMENTARIES:
            case DROP_EFFECTLESS_STORES:
            case ELEMSORT:
            case ELSE:
            case EMPTYBRACKETS:
            case ENUM_CONST:
            case EQUALS:
            case EQUAL_UNIQUE:
            case EQV:
            case EXISTS:
            case EXP:
            case EXTENDS:
            case FALSE:
            case FIELDTYPE:
            case FINAL:
            case FIND:
            case FORALL:
            case FORMULA:
            case FREELABELIN:
            case FUNCTIONS:
            case GENERIC:
            case GREATER:
            case GREATEREQUAL:
            case HASLABEL:
            case HASSORT:
            case HASSUBFORMULAS:
            case HELPTEXT:
            case HEURISTICS:
            case HEURISTICSDECL:
            case HEX:
            case HEX_LITERAL:
            case IDCHAR:
            case IDENT:
            case IF:
            case IFEX:
            case IMP:
            case IMPLICIT_IDENT:
            case INCLUDE:
            case INCLUDELDTS:
            case INSEQUENTSTATE:
            case INSTANTIATE_GENERIC:
            case INVARIANTS:
            case IN_TYPE:
            case ISARRAY:
            case ISARRAYLENGTH:
            case ISCONSTANT:
            case ISENUMTYPE:
            case ISINDUCTVAR:
            case ISLOCALVARIABLE:
            case ISOBSERVER:
            case ISREFERENCE:
            case ISREFERENCEARRAY:
            case ISSTATICFIELD:
            case ISSUBTYPE:
            case ISTHISREFERENCE:
            case IS_ABSTRACT_OR_INTERFACE:
            case JAVABLOCK:
            case JAVASOURCE:
            case KEYSETTINGS:
            case LBRACE:
            case LBRACKET:
            case LEMMA:
            case LESS:
            case LESSEQUAL:
            case LESS_DISPATCH:
            case LETTER:
            case LGUILLEMETS:
            case LOCSET:
            case LPAREN:
            case METADISJOINT:
            case MINUS:
            case MODALITY:
            case MODALITYEND:
            case MODALOPERATOR:
            case MODIFIES:
            case NEW:
            case NEWLABEL:
            case NODEFAULTCLASSES:
            case NONINTERACTIVE:
            case NOT:
            case NOTFREEIN:
            case NOT_:
            case NOT_EQUALS:
            case NUM_LITERAL:
            case ONEOF:
            case OPTIONSDECL:
            case OR:
            case PARALLEL:
            case PERCENT:
            case PLUS:
            case PREDICATES:
            case PRIMES:
            case PRIMES_OR_CHARLITERAL:
            case PROBLEM:
            case PROFILE:
            case PROGRAM:
            case PROGRAMVARIABLES:
            case PROOF:
            case PROOFOBLIGATION:
            case PROOFSCRIPT:
            case PROXY:
            case QUOTED_STRING_LITERAL:
            case RBRACE:
            case RBRACKET:
            case REPLACEWITH:
            case RGUILLEMETS:
            case RPAREN:
            case RULES:
            case SAME:
            case SAMEUPDATELEVEL:
            case SCHEMAVAR:
            case SCHEMAVARIABLES:
            case SEMI:
            case SEQ:
            case SEQARROW:
            case SIMPLIFY_IF_THEN_ELSE_UPDATE:
            case SKOLEMFORMULA:
            case SKOLEMTERM:
            case SLASH:

            case SORTS:
            case STAR:
            case STATIC:
            case STATICMETHODREFERENCE:
            case STRICT:
            case STRING_LITERAL:
            case SUBST:
            case SUCCEDENTPOLARITY:
            case TERM:
            case TERMLABEL:
            case THEN:
            case TILDE:
            case TRANSFORMERS:
            case TRIGGER:
            case TRUE:
            case TYPEOF:
            case UNIQUE:
            case UPDATE:
            case UTF_EMPTY:
            case UTF_IN:
            case UTF_INTERSECT:
            case UTF_PRECEDES:
            case UTF_SETMINUS:
            case UTF_SUBSET:
            case UTF_UNION:
            case VARCOND:
            case VARIABLES:
            case VOCAB:
            case WITHOPTIONS:
                return RESERVED_WORD;

            case SL_COMMENT:
            case ML_COMMENT:
                return COMMENT_MULTILINE;

            case KeYLexer.VARIABLE:
                return TokenTypes.VARIABLE;
            case WS:
                return WHITESPACE;
            default:
                return ERROR_IDENTIFIER;
        }
        /*
        int NULL							= 0;

        int COMMENT_EOL						= 1;
        int COMMENT_MULTILINE				= 2;
        int COMMENT_DOCUMENTATION			= 3;
        int COMMENT_KEYWORD					= 4;
        int COMMENT_MARKUP					= 5;

        int RESERVED_WORD					= 6;
        int RESERVED_WORD_2					= 7;

        int FUNCTION						= 8;

        int LITERAL_BOOLEAN					= 9;
        int LITERAL_NUMBER_DECIMAL_INT		= 10;
        int LITERAL_NUMBER_FLOAT			= 11;
        int LITERAL_NUMBER_HEXADECIMAL		= 12;
        int LITERAL_STRING_DOUBLE_QUOTE		= 13;
        int LITERAL_CHAR					= 14;
        int LITERAL_BACKQUOTE				= 15;

        int DATA_TYPE						= 16;

        int VARIABLE						= 17;

        int REGEX							= 18;

        int ANNOTATION						= 19;

        int IDENTIFIER						= 20;

        int WHITESPACE						= 21;

        int SEPARATOR						= 22;

        int OPERATOR						= 23;

        int PREPROCESSOR					= 24;

        int MARKUP_TAG_DELIMITER			= 25;
        int MARKUP_TAG_NAME					= 26;
        int MARKUP_TAG_ATTRIBUTE			= 27;
        int MARKUP_TAG_ATTRIBUTE_VALUE		= 28;
        int MARKUP_COMMENT					= 29;
        int MARKUP_DTD						= 30;
        int MARKUP_PROCESSING_INSTRUCTION	= 31;
        int MARKUP_CDATA_DELIMITER			= 32;
        int MARKUP_CDATA					= 33;
        int MARKUP_ENTITY_REFERENCE			= 34;

        int ERROR_IDENTIFIER				= 35;
        int ERROR_NUMBER_FORMAT				= 36;
        int ERROR_STRING_DOUBLE 			= 37;
        int ERROR_CHAR						= 38;

        int DEFAULT_NUM_TOKEN_TYPES = 39;
        
         */
    }

    @Override
    protected Lexer createLexer(String toString) {
        return new KeYLexer(new ANTLRStringStream(toString));
    }
}
