grammar Casl;

/*
spec Strict Partial Order =
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

basic_spec:  basic_items* ;
basic_items: sig_items
    | 'free' 'types' (datatype_decl ';')*
    | 'generated' 'types' (datatype_decl ';')*
    | 'generated' '{' sig_items*'}'
    | 'vars' (var_decl';')*
    | 'forall' (var_decl ';')*
       '.' formula ('.' formula)*
    |       '.' formula ('.' formula)*
    ;

sig_items:  'sorts' (sort_item ';')*
          | 'ops' (op_item ';')*
          | 'preds' (pred_item ';')*
          | 'types' (datatype_decl ';')*
          ;

sort_item: sort (',' sort)*;
op_item: op_name (',' op_name)* ':' op_type
         | op_name (',' op_name)* ':' op_type ',' op_attr (',' op_attr)*
         | op_name op_head '=' term
      ;

op_type: sort ('*' sort)* '->' sort | sort
        | sort ('*' sort)* '->' '?' sort  | '?' sort
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
datatype_decl: sort '::=' alternative ('|' alternative);
alternative: op_name (('(' component (';' component)* ')') '?'?)?;
component: (op_name (',' op_name) ':' '?'? )? sort;
var_decl: var (',' var)* ':' sort;
formula: quantifier var_decl(';'var_decl)* '.' formula
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
| mixfix+
;

quantifier: 'forall' | 'exists' | 'exists!';
terms: term (',' term)*;
term: mixfix;
mixfix: token | literal | place | qual_pred_name | qual_var_name | qual_op_name
      | term ':' sort | term 'when' formula 'else' term
      | '(' terms ')'
      | '[' terms ']'
      | '{' terms '}'
      | '[' ']'
      | '{' '}'
      ;

qual_var_name :  '(' 'var' var ':' sort ')';
qual_pred_name :  '(' 'pred' pred_name ':' pred_type ')';
qual_op_name :  '(' 'op' op_name ':' op_type ')';
sort:sort_id;
op_name:id;
pred_name:id;
var:simple_id;
token: WORDS | DOT_WORDS | DIGIT | SIGNS | QUOTED_CHAR;
literal: STRING | DIGITS |FRACTION|FLOATING;
place: '__';
sort_id: WORDS;
simple_id: WORDS;
id: mix_token+;
mix_token: token | place
      | '[' id? ']'
      | '{' id? '}' ;


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
//OR:'\\/';
//AND:'/\\';

MID:'|';
MAPSTO: '|->';
EEQ:'=e=';

WORDS: WORD ('_' WORD)+;
DOT_WORDS:'.' WORDS;
WORD: WORD_CHAR+;

fragment WORD_CHAR: LETTER | '\'' | DIGIT;
fragment LETTER: [a-zA-Z];
fragment DIGIT: [0-9];

SIGNES: SIGN+;
fragment SIGN: '+' | '-' | '*' | '/' | '\\' | '&' | '=' | '<' | '>' |
         '!'|'?'|':'|'.'|'$'|'@'|'#'|'^'|'~';

QUOTED_CHAR: '\'' . '\'';

NUMBER: DIGIT+;
FRACTION: NUMBER '.' NUMBER;
FLOATING: (NUMBER|FRACTION) [eE] ('+'|'-')? NUMBER;

STRING_LITERAL:'"' ('\\' . | ~( '"' | '\\') )* '"' ;
WS:  [ \t\n\r\u00a0]+ -> channel(HIDDEN); //U+00A0 = non breakable whitespace


fragment PATH_CHAR: 
         [A-Za-z$-_@.&+!*"'(),:~] | ('%' HEX_CHAR HEX_CHAR);
fragment HEX_CHAR:[A-Fa-f0-9];
fragment PATH_WORD: PATH_CHAR+;
fragment PATH: PATH_WORD ('/' PATH_WORD);
URL: ('http://'|'ftp://'|'file:///') PATH;
COMMENT: '%%'(~'\n')* -> channel(HIDDEN);
         