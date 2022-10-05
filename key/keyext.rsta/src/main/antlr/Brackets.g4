grammar Brackets;

@header {
    package antlr;
}

LBRACKET:
    '{'
    ;

RBRACKET:
    '}'
    ;

WEIRD:
    'weird'
    ;

WS:
    (' '|'\r'|'\t'|'\n') -> channel(HIDDEN)
    ;

NO_MATCH:
    . //-> skip leads to the stuff not being printed, but it's still in the input stream
    ;

bracket:
    LBRACKET | RBRACKET
    ;



