grammar ADTLang;

/*
theory 'a {
  type List = Nil | Cons(any, List);
}

*/

file: theory*;

theory: 'theory' id* '{' datatype+ function* '}';

datatype: 'type' id '=' constructor ('|' constructor)*  ;

constructor: name=id ( '(' a+=id (',' a+=id)* ')' )?;

function:
  'fun' name=id '(' arg (',' arg)* ')' '=' expression ';';

arg: (constructor|var=id) ':' t=id;

expression :
      'if' expression 'then' expression 'else' expression
   |  expression relop expression
   |  expression  POW expression
   |  expression  (TIMES | DIV)  expression
   |  expression  (PLUS | MINUS) expression
   |  LPAREN expression RPAREN
   |  primary
   ;

primary:
   | (PLUS | MINUS) primary
   | scientific
   | id ( '(' expression (',' expression)* ')' )?
   ;

scientific: SCIENTIFIC_NUMBER;
relop: EQ | GT | LT;

SCIENTIFIC_NUMBER: NUMBER (E SIGN? UNSIGNED_INTEGER)?;
fragment NUMBER
   : ('0' .. '9') + ('.' ('0' .. '9') +)?
   ;

fragment UNSIGNED_INTEGER
   : ('0' .. '9')+
   ;


fragment E
   : 'E' | 'e'
   ;


fragment SIGN
   : ('+' | '-')
   ;


LPAREN: '(';
RPAREN: ')';
PLUS: '+';
MINUS: '-';
TIMES: '*';
DIV: '/';
GT: '>';
LT: '<';
EQ: '=';
POINT: '.';
POW: '^';
id: IDENT;

STRING_LITERAL:'"' ('\\' . | ~( '"' | '\\') )* '"' ;
//TIDENT: '\'' [a-zA-Z_]+;
IDENT: '\''? [a-zA-Z_]+;
WS:  [ \t\n\r\u00a0]+ -> channel(HIDDEN); //U+00A0 = non breakable whitespace
