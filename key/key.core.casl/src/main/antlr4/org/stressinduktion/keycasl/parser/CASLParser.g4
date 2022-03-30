parser grammar CASLParser;

options {
    tokenVocab=CASLLexer;
}

@header {
import java.util.Collection;
import java.util.Set;
import java.util.HashSet;
}

basic_spec
    : basic_items+
    | '{' '}'
    ;

basic_items
    : sig_items # BasicItemSigItems
    | 'free' ('type'|'types') datatype_decl (';' datatype_decl)* ';'? # BasicItemDataTypeDecl
    | 'generated' ('type'|'types') datatype_decl (';' datatype_decl)* ';'? # BasicItemDataTypeDecl
    | 'generated' '{' sig_items+ '}' ';'? # BasicItemGeneratedSigItems
    | ('var'|'vars') var_decl (';' var_decl)* ';'? # BasicItemVars
    | 'forall' var_decl (';' var_decl)* '.' formula /* ('.' formula)* */ ';'? # BasicItemForallFormula
    | '.' formula ('.' formula)* ';'? # BasicItemFormula
    ;

sig_items
    : ('sort'|'sorts') sort_item (';' sort_item)* ';'? # SigItemSort
    | ('op'|'ops') op_item (';' op_item)* ';'? # SigItemOp
    | ('preds'|'pred') pred_item (';' pred_item)* ';'? # SigItemPred
    | ('type'|'types') datatype_decl (';' datatype_decl)* ';'? # SigItemType
    ;

sort_item
    : sort (',' sort)*
    | sort (',' sort)* '<' sort // subsorting
    | sort '=' '{' var ':' sort '.' formula '}' // subsorting
    | sort ('=' sort)+ // subsorting
    ;

op_item
    : op_name (',' op_name)* ':' op_type (',' op_attr)*
    | op_name op_head '=' term
    ;

op_type
    : args+=sort ('*' args+=sort)* '->' '?'? retSort=sort
    | '?'? retSort=sort
    ;

op_attr
    : 'assoc'
    | 'comm'
    | 'idem'
    | 'unit' term
    ;

op_head
    : '(' arg_decl (';' arg_decl)* ')' ':' '?'? sort
    | ':' '?'? sort
    ;

arg_decl
    : var (',' var)* ':' sort
    ;

pred_item
    : pred_name (',' pred_name)* ':' pred_type
    | pred_name pred_head '<=>' formula
    | pred_name '<=>' formula
    ;

pred_type
    : sort ('*' sort)*
    | '(' ')'
    ;

pred_head
    : '(' arg_decl (';' arg_decl)* ')'
    ;

datatype_decl
    : sort '::=' alternative ('|' alternative)*
    ;

alternative
    : op_name '(' component (';' component)* ')' '?'?
    | op_name
    | ('sort'|'sorts') sort (',' sort)* // subsorting
    ;

component
    : op_name (',' op_name)* (':?' | ':' '?'?) sort
    | sort
    ;

var_decl
    : var (',' var)* ':' sort
    ;

formula
    : 'not' formula # formulaNot
    | formula ('/\\' formula)+ # formulaConj
    | formula ('\\/' formula)+ # formulaDisj
    |<assoc=right> formula '=>' formula # formulaImpl
    |<assoc=left> formula 'if' formula # formulaIf
    | formula '<=>' formula # formulaEq
    | quantifier var_decl (';' var_decl)* '.' formula # formulaQ
    | 'true' # formulaTrue
    | 'false' # formulaFalse
    | 'def' term # formulaDefTerm // substitution?
    | term '=e=' term # formulaExistEqTerm
    | term '=' term # formulaEqTerm // in beide richtungen
    | '(' formula ')' # formulaP
    | qual_pred_name terms? # formulaQualPredName
    | term 'in' sort # formulaUnsupported  // subsorting
    ;

quantifier
    : 'forall'
    | 'exists'
    | 'exists!'
    ;

terms
    : term (',' term)*
    ;

// mixfix notation and context sensitive parsing is not yet done here - see CASL Reference Manual
term
    : literal # termLiteral
    | qual_var_name # termQualVarName
    | qual_op_name '(' terms ')' # termQualOpName
    | term ':' sort # termSort
    | term 'as' sort # termAs
    | term 'when' formula 'else' term # termWhen
    | '(' term ')' # termP
    | id '(' terms ')' # termFunc
    | id # termId
    // continue casl reference pp. 96
    ;

qual_var_name
    : '(' 'var' var ':' sort ')'
    ;

qual_pred_name
    : '(' 'pred' pred_name ':' pred_type ')'
    ;

qual_op_name
    : '(' 'op' op_name ':' op_type ')'
    ;

sort
    : sort_id
    ;

op_name
    : id
    ;

pred_name
    : id
    ;

var
    : simple_id
    ;

token
    : WORDS
    | DOT_WORDS
    | DIGIT
    | signs
    | STAR
    | QUOTED_CHAR
    ;

literal
    : STRING
    | DIGITS
    | FRACTION
    | FLOATING
    | TRUE
    | FALSE
    ;

place
    : '__'
    ;

sort_id
    : WORDS # sortId
    | WORDS ('[' id (',' id)* ']')? # sortIdUnsupported
    ;

simple_id
    : WORDS
    ;

id
    : mix_token+
    ;

mix_token
    : token
    | place
    | '[' id? ']'
    | '{' id? '}'
    | '[' id (',' id)* ']' // structured
    ;

// structured
spec
    : 'free' group_spec # specUnsupported
    | 'closed' group_spec # specUnsupported
    | spec renaming # specUnsupported
    | spec restriction # specUnsupported
    | 'local' spec 'within' spec # specUnsupported
    | spec ('and' spec)+ # specUnsupported
    | spec ('then' spec)+ # specUnsupported
    | basic_spec # specBasicSpec
    | group_spec # specUnsupported
    ;

group_spec
    : '{' spec '}'
    | spec_name ('[' fit_arg ']')*
    ;

renaming
    : 'with' symb_map_items (',' symb_map_items)*
    ;

restriction
    : 'hide' symb_items (',' symb_items)*
    | 'reveal' symb_map_items (',' symb_map_items)*
    ;

spec_defn
    : 'spec' spec_name '=' spec 'end'? # specDefnPlain
    | 'spec' spec_name some_generics '=' spec 'end'? # specDefnUnsupported
    ;

// custom rule for spec_defn with EOF
spec_defn_eof
    : spec_defn EOF
    ;


some_generics
    : some_params some_imported?
    ;

some_params
    : ('[' spec ']')+
    ;

some_imported
    : 'given' group_spec (',' group_spec)*
    ;

fit_arg
    : spec 'fit' symb_map_items (',' symb_map_items)*
    | spec
    | 'view' view_name ('[' fit_arg ']')*
    ;

view_defn
    : 'view' view_name ':' view_type 'end'?
    | 'view' view_name ':' view_type '=' symb_map_items (',' symb_map_items)* 'end'?
    | 'view' view_name some_generics ':' view_type 'end'?
    | 'view' view_name some_generics ':' view_type '=' symb_map_items (',' symb_map_items)* 'end'?
    ;

view_type
    : group_spec 'to' group_spec
    ;

symb_items
    : symb
    | some_symb_kind symb (',' symb)*
    ;

symb_map_items
    : symb_or_map
    | some_symb_kind symb_or_map (',' symb_or_map)*
    ;

some_symb_kind
    : ('sort'|'sorts')
    | ('op'|'ops')
    | ('pred'|'preds')
    ;

symb
    : id
    | id ':' type
    ;

type
    : op_type
    | pred_type
    ;

symb_map
    : symb '|->' symb
    ;

symb_or_map
    : symb
    | symb_map
    ;

spec_name
    : simple_id
    ;

view_name
    : simple_id
    ;

// architectural specification
arch_spec_defn
    : 'arch' 'spec' arch_spec_name '=' arch_spec 'end'?
    ;

arch_spec
    : basic_arch_spec
    | group_arch_spec
    ;

group_arch_spec
    : '{' arch_spec '}'
    | arch_spec_name
    ;

basic_arch_spec
    : ('unit'|'units') unit_decl_defn (';' unit_decl_defn)* ';'? 'result' unit_expression ';'?
    ;

unit_decl_defn
    : unit_decl
    | unit_defn
    ;

unit_decl
    : unit_name ':' unit_spec 'given' group_unit_term (',' group_unit_term)*
    | unit_name ':' unit_spec
    ;

unit_defn
    : unit_name '=' unit_expression
    ;

unit_spec_defn
    : 'unit' 'spec' spec_name '=' unit_spec 'end'?
    ;

unit_spec
    : group_spec
    | group_spec ('*' group_spec)* '->' group_spec
    | 'arch' 'spec' group_arch_spec
    | 'closed' unit_spec
    ;

unit_expression
    : 'lambda' unit_binding (';' unit_binding)* '.' unit_term
    | unit_term
    ;

unit_binding
    : unit_name ':' unit_spec
    ;

unit_term
    : unit_term renaming
    | unit_term restriction
    | unit_term ('and' unit_term)+
    | 'local' unit_defn (';' unit_defn)* ';'? 'within' unit_term
    | group_unit_term
    ;

group_unit_term
    : '{' unit_term '}'
    | unit_name ('[' fit_arg_unit ']')*
    ;

fit_arg_unit
    : unit_term
    | unit_term 'fit' symb_map_items (',' symb_map_items)*
    ;

arch_spec_name
    : simple_id
    ;

unit_name
    : simple_id
    ;

lib_defn
    : 'library' lib_name lib_item*
    ;

lib_defn_eof
    : lib_defn EOF
    ;

lib_item
    : spec_defn # libItemspecDefn
    | view_defn # libItemUnsupported
    | arch_spec_defn # libItemUnsupported
    | unit_spec_defn # libItemUnsupported
    | 'from' lib_name 'get' item_name_or_map (',' item_name_or_map)* 'end'? # libItemUnsupported
    ;

item_name_or_map
    : item_name
    | item_name '|->' item_name
    ;

item_name
    : simple_id
    ;

lib_name
    : lib_id version_number?
    ;

version_number
    : VERSION VERSION_NUM
    ;

lib_id
    : URL
    | PATH
    ;

sign_user
    : '+' | '-' | '*' | '/' | '\\' | '&' | '<' | '>'
    | '!' | '?' | '$' | '@' | '#' | '^' | '~' | '->'
    ;

sign_comb
    : '=' | ':' | '.' | '|'
    ;

reserved_signs
    : ':' | ':?' | '::=' | '=' | '=>' | '<=>' | '.' | '|' | '|->' | '\\/' | '/\\'
    ;

all_signs
    : reserved_signs | sign_user | sign_comb;

signs
    : all_signs+ (sign_comb|reserved_signs) all_signs*
    | all_signs* (sign_comb|reserved_signs) all_signs+
    | sign_user+
    ;
