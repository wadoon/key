lexer grammar Testlexer;

HUI: 'test';
COMMENT: '/*' -> pushMode(comment);
DEFAULT: .;

mode comment;
END: '*/' -> type(COMMENT), popMode;
TEST: 'test';
CONTENT: . -> type(COMMENT);
