grammar ProofCollection;

parserEntryPoint: settingAssignment* (g=group | file=testFile)* EOF;

settingAssignment: k=Identifier '=' v=valueDeclaration;

valueDeclaration: Identifier|PathString|Number|QuotedString;

group: 'group' nameToken=Identifier '{' settingAssignment* t+=testFile* '}';

testFile: (PROVABLE| NOTPROVABLE | LOADABLE | NOTLOADABLE) ':'?  path=valueDeclaration;

/*
 * Section for non-whitespace lexer rules. Lexer rules start with uppercase letters.
 * Whitespace rules can be found at the end of the file. I put them in a separate section, since
 * they are written to hidden channel.
 */

PROVABLE:'provable';
NOTPROVABLE: 'notprovable';
LOADABLE: 'loadable';
NOTLOADABLE:'notloadable';

Identifier:  IdentifierStart( IdentifierStart | Digit | '.')*;
Number: Digit+;
QuotedString: '"' (EscapedQuote | ~('\\' | '"'))* '"';

/*
 * This lexer rule is for a string that is neither quoted, nor an identifier or a number.
 * As its name suggests, intended use is to allow specifying path names.
 * Note: There is a (seemingly inevitable) overlap with Number and Identifier lexer rules.
 *       Depending on input, lexer might create an Identifier token at a place where a path name is expected.
 *       This is considered in parser rule testDeclaration.
 */
PathString: (~('\n' | '\r' | '}' | '{' | '=' | ' ' | '\t' | ':' | '"' | '\\') | EscapedQuote)+;

fragment EscapedQuote: '\\' ('\\' | '"');
fragment IdentifierStart: 'a'..'z' | 'A'..'Z' | '_' | '$';
fragment Digit: '0'..'9';

WS: (' '|'\r'|'\t'|'\u000C'|'\n')+ ->skip;
COMMENT: '/*' .*? '*/' -> skip;
LINE_COMMENT : ('//' | '#') ~('\n'|'\r')* '\r'? '\n' -> skip;
