grammar Casl;

/*
spec StrictPartialOrder =
  %% Let’s start with a simple example !
  sort Elem
  pred < : Elem × Elem %% pred abbreviates predicate
  ∀x , y, z : Elem
  • ¬(x < x )
  %(strict)%
  • x < y ⇒ ¬(y < x )
  %(asymmetric)%
  • x < y ∧ y < z ⇒ x < z
  %(transitive)%
  %{ Note that there may exist x, y such that
  neither x < y nor y < x. }%
end

free types
Nat	::=	0 | sort Pos;
Pos	::=	suc(pre:Nat)
op
pre : Nat ->? Nat
axioms

¬ def pre(0);
forall n:Nat · pre(suc(n)) = n

pred even__ : Nat
var n:Nat
· even 0
· even suc(n) <=> ¬ even n

*/

/*******************************************/
/*3.1.3 Structured Specifications*/
base_spec
    : basic_spec
    | 'free' group_spec
    | 'closed' group_spec
    | 'local' spec 'within' spec
    | group_spec
    ;

spec: base_spec  ( renaming
                 | restriction
                 | ('and' spec)
                 | ('then' spec)
                 )?
    ;

group_spec
    : '{' spec '}'
    | spec_name ('[' fit_arg']')*
    ;

renaming: 'with' symb_map_items (',' symb_map_items)*;
restriction
    : 'hide' symb_items (',' symb_items)*
    | 'reveal' symb_map_items (',' symb_map_items)*
    ;

spec_defn
  : 'spec' spec_name some_generics? '=' spec 'end'?;

some_generics: some_params some_imported?;
some_params: ('[' fit_arg']')+;
some_imported:'given' group_spec (',' group_spec)*;
fit_arg
  : spec ('fit' symb_map_items (',' symb_map_items)*)?
  | 'view' view_name some_params?
  ;

view_defn
  : 'view' view_name  some_generics? ':' view_type
    ('=' symb_map_items (',' symb_map_items)*)?
    'end'?
  ;

view_type: group_spec 'to' group_spec;
symb_items: symb | some_symb_kind symb (',' symb)*;
symb_map_items: symb_or_map | some_symb_kind symb_or_map (',' symb_or_map)*;
some_symb_kind: 'sort'|'sorts'|'op'|'ops'|'pred'|'preds';
symb: id | id ':' type ;
type: op_type | pred_type;
symb_map : symb '|->' symb;
symb_or_map : symb | symb_map;
spec_name: id;
view_name: id;

/*******************************************/
basic_spec:  basic_items+;
basic_items: sig_items
    | ('generated'|'free') ('type'|'types') datatype_decl (';' datatype_decl)* ';'?
    | 'generated' '{' sig_items*'}' ';'?
    | ('var'|'vars') var_decl (';' var_decl)* ';'?
    | 'forall' var_decl (';' var_decl)*
      ('.'|'·') formula (('.'|'·') formula)*
      ';'?
    | ('.'|'·') formula (('.'|'·') formula)* ';'?

    ;

sig_items:  ('sorts'|'sort') sort_item (';' sort_item)* ';'?
          | ('op'|'ops') op_item (';' op_item)* ';'?
          | ('pred'|'preds') pred_item  (';' pred_item )* ';'?
          | ('type'|'types') datatype_decl (';' datatype_decl)* ';'?
          ;

sort_item
    : sort (',' sort)* ('<' sort)?
    | sort '=' '{' var ':' sort '.' formula '}'
    | sort ('=' sort)+
    ;

op_item:   op_name (',' op_name)* ':' op_type (',' op_attr)*
         | op_name op_head '=' term
      ;

op_type: sort ('*' sort)* '->' sort
        | sort
        | sort ('*' sort)* '->' '?' sort
        | '?' sort
        ;

op_attr: 'assoc' | 'comm' | 'idem' | 'unit' term;

op_head: '(' arg_decl (';' arg_decl)* ')' ':' '?'? sort
        | ':' '?'? sort;

arg_decl: var (',' var)* ':' sort;

pred_item: pred_name (',' pred_name)* ':' pred_type
         | pred_name pred_head? '<=>' formula
         ;

pred_type: sort ('*' sort)* | '(' ')';
pred_head: arg_decl (';' arg_decl)*;
datatype_decl: sort '::=' alternative ('|' alternative)*;
alternative
    : op_name ( ('(' component (';' component)* ')') '?'?)?
    | ('sort'|'sorts') sort (',' sort)*
    |
    ;

component: (op_name (',' op_name)* ':' '?'? )? sort;
var_decl: var (',' var)* ':' sort;
formula
    : quantifier var_decl(';'var_decl)* '.' formula
    | term 'in' sort
    | formula ('/\\' formula)+
    | formula ('\\/' formula)+
    | formula ('=>' formula)
    | formula ('if' formula)
    | formula ('<=>' formula)
    | 'not' formula
    | 'def' formula
    | 'true' | 'false'
    | term ('=e=' term)
    | term ('=' term)
    | term+
;

quantifier: 'forall' | 'exists' | 'exists!';
terms: term (',' term)*;
term
    : token | literal | place | qual_pred_name | qual_var_name | qual_op_name
    | '(' terms ')'
    | '[' terms ']'
    | '{' terms '}'
    | '[' ']'
    | '{' '}'
    | term 'as' sort
    | term ':' sort
    | term 'when' formula 'else' term
    ;

qual_var_name :  '(' 'var' var ':' sort ')';
qual_pred_name :  '(' 'pred' pred_name ':' pred_type ')';
qual_op_name :  '(' 'op' op_name ':' op_type ')';
sort:sort_id;
op_name:id;
pred_name:id;
var:simple_id;
token: WORDS | WORD | DOT_WORDS | signs | NUMBER | QUOTED_CHAR;
signs: SIGNS | '*';
literal: STRING | NUMBER |FRACTION|FLOATING;
place: '__';
sort_id: WORD | WORDS ('[' id (',' id)']')?;
simple_id: WORD | WORDS;
id: mix_token+;
mix_token
      : token
      | place
      | '[' id? ']'
      | '{' id? '}'
      ;


AND:'and';
ARCH:'arch';
AS:'as';
AXIOM:'axiom';
AXIOMS:'axioms';
CLOSED:'closed';
DEF:'def';
ELSE:'else';
END:'end';
EXISTS:'exists';
FALSE:'false';
FIT:'fit';
FORALL:'forall';
FREE:'free';
FROM:'from';
GENERATED:'generated';
GET:'get';
GIVEN:'given';
HIDE:'hide';
IF:'if';
IN:'in';
LAMBDA:'lambda';
LIBRARY:'library';
LOCAL:'local';
NOT:'not';
OP:'op';
OPS:'ops';
PRED:'pred';
PREDS:'preds';
RESULT:'result';
REVEAL:'reveal';
SORT:'sort';
SORTS:'sorts';
SPEC:'spec';
THEN:'then';
TO:'to';
TRUE:'true';
TYPE:'type';
TYPES:'types';
UNIT:'unit';
UNITS:'units';
VAR:'var';
VARS:'vars';
VERSION:'version';
VIEW:'view';
WHEN:'when';
WITH:'with';
WITHIN:'within';
ASSOC:'assoc';
COMM:'comm';
IDEM:'idem';


COLON: ':';
QUESTION:':?';
ASSIGN:'::=';
EQ:'=';
IMPL:'=>';
EQUIV:'<=>';
DOT:'.';
CDOT:'·';
LPAREN:'(';
RPAREN:')';
LBRACE:'{';
RBRACE:'}';
RBRACKET:']';
LBRACKET:'[';
STAR:'*';


MID:'|';
MAPSTO: '|->';
EEQ:'=e=';
PLACE:'__';
WORD:'...fsda.fsda.fsda.fsdaklkjsda';
WORDS: (WORD_CHAR) (WORD_CHAR|DIGIT)*;
//WORDS: WORD ('_' (WORD|DIGIT))+;
DOT_WORDS:'.' WORDS;
//WORD: WORD_CHAR+;

fragment WORD_CHAR: LETTER | '\'' | '_';
fragment LETTER: [a-zA-Z];
fragment DIGIT: [0-9];

SIGNS: SIGN+;
fragment SIGN: '+' | '-' | '*' | '/' | '\\' | '&' | '=' | '<' | '>' |
                '!'| '?' | ':' | '.' | '$'  | '@' | '#' | '^' | '~'
                ;
QUOTED_CHAR: '\'' . '\'';

NUMBER: DIGIT+;
FRACTION: NUMBER '.' NUMBER;
FLOATING: (NUMBER|FRACTION) [eE] ('+'|'-')? NUMBER;

STRING:'"' ('\\' . | ~( '"' | '\\') )* '"' ;

COMMENT_LINE: '%%' (~[\n\r])* -> channel(HIDDEN);
COMMENT_GROUP: '%{' .*? '}%' -> channel(HIDDEN);
COMMENT_OUT: '%[' .*? ']%' -> channel(HIDDEN);

ANNOTATION_LINE: '%' WORDS (~[\n\r])* -> channel(HIDDEN);
ANNOTATION_GROUP: '%' WORDS '(' .*? ')%' -> channel(HIDDEN);
LABEL: '%(' (~[\n\r])* ')%' -> channel(HIDDEN);

WS:  [ \t\n\r\u00a0]+ -> channel(HIDDEN);


/*fragment PATH_CHAR: [A-Za-z$_@.&+!*"'(),:~-] | ('%' HEX_CHAR HEX_CHAR);
fragment HEX_CHAR:  [A-Fa-f0-9];
fragment PATH_WORD: PATH_CHAR+;
fragment PATH: PATH_WORD ('/' PATH_WORD);
URL: ('http://'|'ftp://'|'file:///') PATH;
COMMENT: '%%'(~'\n')* -> channel(HIDDEN);
       */