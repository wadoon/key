// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2016 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

lexer grammar KeYCommonLexer ;

@header {
	package org.key_project.common.core.parser;
}

/**
 * The common lexer for declarations, terms, formulae, Taclets, etc.
 */

// Keywords used in sort declarations
SORTS
	: '\\sorts' ;

GENERIC
	: '\\generic' ;

PROXY
	: '\\proxy' ;

EXTENDS
	: '\\extends' ;

ONEOF
	: '\\oneof' ;

ABSTRACT
	: '\\abstract' ;

// Keywords used in schema variable declarations
SCHEMAVARIABLES
	: '\\schemaVariables' ;

SCHEMAVAR
	: '\\schemaVar' ;

MODALOPERATOR
	: '\\modalOperator' ;

PROGRAM
	: '\\program' ;

FORMULA
	: '\\formula' ;

TERM
	: '\\term' ;

UPDATE
	: '\\update' ;

VARIABLES
	: '\\variables' ;

VARIABLE
	: '\\variable' ;

SKOLEMTERM
	: '\\skolemTerm' ;

SKOLEMFORMULA
	: '\\skolemFormula' ;

TERMLABEL
	: '\\termlabel' ;

// used in contracts
MODIFIES
	: '\\modifies' ;

// Keywords used in program variable declarations
PROGRAMVARIABLES
	: '\\programVariables' ;

// Keywords for varcond and related stuff
VARCOND
	: '\\varcond' ;

APPLY_UPDATE_ON_RIGID
	: '\\applyUpdateOnRigid' ;

DEPENDINGON
	: '\\dependingOn' ;

DISJOINTMODULONULL
	: '\\disjointModuloNull' ;

DROP_EFFECTLESS_ELEMENTARIES
	: '\\dropEffectlessElementaries' ;

DROP_EFFECTLESS_STORES
	: '\\dropEffectlessStores' ;

SIMPLIFY_IF_THEN_ELSE_UPDATE
	: '\\simplifyIfThenElseUpdate' ;

ENUM_CONST
	: '\\enumConstant' ;

FREELABELIN
	: '\\freeLabelIn' ;

HASSORT
	: '\\hasSort' ;

FIELDTYPE
	: '\\fieldType' ;

FINAL
	: '\\final' ;

ELEMSORT
	: '\\elemSort' ;

HASLABEL
	: '\\hasLabel' ;

HASSUBFORMULAS
	: '\\hasSubFormulas' ;

ISARRAY
	: '\\isArray' ;

ISARRAYLENGTH
	: '\\isArrayLength' ;

ISCONSTANT
	: '\\isConstant' ;

ISENUMTYPE
	: '\\isEnumType' ;

ISINDUCTVAR
	: '\\isInductVar' ;

ISLOCALVARIABLE
	: '\\isLocalVariable' ;

ISOBSERVER
	: '\\isObserver' ;

DIFFERENT
	: '\\different' ;

METADISJOINT
	: '\\metaDisjoint' ;

ISTHISREFERENCE
	: '\\isThisReference' ;

DIFFERENTFIELDS
	: '\\differentFields' ;

ISREFERENCE
	: '\\isReference' ;

ISREFERENCEARRAY
	: '\\isReferenceArray' ;

ISSTATICFIELD
	: '\\isStaticField' ;

ISSUBTYPE
	: '\\sub' ;

EQUAL_UNIQUE
	: '\\equalUnique' ;

NEW
	: '\\new' ;

NEWLABEL
	: '\\newLabel' ;

CONTAINS_ASSIGNMENT
	: '\\containsAssignment' ;

// label occurs again for character `!'
NOT_
	: '\\not' ;

NOTFREEIN
	: '\\notFreeIn' ;

SAME
	: '\\same' ;

STATIC
	: '\\static' ;

STATICMETHODREFERENCE
	: '\\staticMethodReference' ;

STRICT
	: '\\strict' ;

TYPEOF
	: '\\typeof' ;

INSTANTIATE_GENERIC
	: '\\instantiateGeneric' ;

// Quantifiers, binding, substitution
FORALL
	: '\\forall'
	| '\u2200' ;

EXISTS
	: '\\exists'
	| '\u2203' ;

SUBST
	: '\\subst' ;

IF
	: '\\if' ;

IFEX
	: '\\ifEx' ;

THEN
	: '\\then' ;

ELSE
	: '\\else' ;

// inclusion and stuff, things that (usually) come at the beginning
// of the file
INCLUDE
	: '\\include' ;

INCLUDELDTS
	: '\\includeLDTs' ;

CLASSPATH
	: '\\classpath' ;

BOOTCLASSPATH
	: '\\bootclasspath' ;

NODEFAULTCLASSES
	: '\\noDefaultClasses' ;

JAVASOURCE
	: '\\javaSource' ;

WITHOPTIONS
	: '\\withOptions' ;

OPTIONSDECL
	: '\\optionsDecl' ;

KEYSETTINGS
	: '\\settings' ;

PROFILE
	: '\\profile' ;

// Those guys can stay being keywords
//TRUE
//	: 'true' ;

//FALSE
//	: 'false' ;

// Keywords related to taclets
SAMEUPDATELEVEL
	: '\\sameUpdateLevel' ;

INSEQUENTSTATE
	: '\\inSequentState' ;

ANTECEDENTPOLARITY
	: '\\antecedentPolarity' ;

SUCCEDENTPOLARITY
	: '\\succedentPolarity' ;

CLOSEGOAL
	: '\\closegoal' ;

HEURISTICSDECL
	: '\\heuristicsDecl' ;

NONINTERACTIVE
	: '\\noninteractive' ;

DISPLAYNAME
	: '\\displayname' ;

HELPTEXT
	: '\\helptext' ;

REPLACEWITH
	: '\\replacewith' ;

ADDRULES
	: '\\addrules' ;

ADDPROGVARS
	: '\\addprogvars' ;

HEURISTICS
	: '\\heuristics' ;

FIND
	: '\\find' ;

ADD
	: '\\add' ;

ASSUMES
	: '\\assumes' ;

TRIGGER
	: '\\trigger' ;

AVOID
	: '\\avoid' ;

PREDICATES
	: '\\predicates' ;

FUNCTIONS
	: '\\functions' ;

TRANSFORMERS
	: '\\transformers' ;

UNIQUE
	: '\\unique' ;

RULES
	: '\\rules' ;

AXIOMS
	: '\\axioms' ;

PROBLEM
	: '\\problem' ;

CHOOSECONTRACT
	: '\\chooseContract' ;

PROOFOBLIGATION
	: '\\proofObligation' ;

PROOF
	: '\\proof' ;

PROOFSCRIPT
	: '\\proofScript' ;

CONTRACTS
	: '\\contracts' ;

INVARIANTS
	: '\\invariants' ;

// Taclet annotations (see TacletAnnotations.java for more details)
LEMMA
	: '\\lemma' ;

// The first two guys are not really meta operators, treated separately
IN_TYPE
	: '\\inType' ;

IS_ABSTRACT_OR_INTERFACE
	: '\\isAbstractOrInterface' ;

CONTAINERTYPE
	: '\\containerType' ;

LIMITED
	: '$lmtd' ;

// types that need to be declared as keywords
LOCSET
	: '\\locset' ;

SEQ
	: '\\seq' ;

BIGINT
	: '\\bigint' ;

// Unicode symbols for special functions/predicates
UTF_PRECEDES
	: '\u227A' ;

UTF_IN
	: '\u220A' ;

UTF_EMPTY
	: '\u2205' ;

UTF_UNION
	: '\u222A' ;

UTF_INTERSECT
	: '\u2229' ;

UTF_SUBSET
	: '\u2286' ;

UTF_SETMINUS
	: '\u2216' ;

fragment VOCAB
	: '\u0003'..'\u0377' ;

SEMI
	: ';' ;

SLASH
	: '/' ;

BACKSLASH
	: '\\' ;

COLON
	: ':' ;

DOUBLECOLON
	: '::' ;

ASSIGN
	: ':=' ;

DOT
	: '.' ;

DOTRANGE
	: '.' '.' ;

COMMA
	: ',' ;

LPAREN
	: '(' ;

RPAREN
	: ')' ;

LBRACE
	: '{' ;

RBRACE
	: '}' ;

LBRACKET
	: '[' ;

RBRACKET
	: ']' ;

EMPTYBRACKETS
	: '[' ']' ;

AT
	: '@' ;

PARALLEL
	: '||' ;

OR
	: '|'
	| '\u2228' ;

AND
	: '&'
	| '\u2227' ;

NOT
	: '!'
	| '\u00AC' ;

IMP
	: '->'
	| '\u2192' ;

EQUALS
	: '=' ;

NOT_EQUALS
	: '!='
	| '\u2260' ;

SEQARROW
	: '==>' ;

EXP
	: '^' ;

TILDE
	: '~' ;

PERCENT
	: '%' ;

STAR
	: '*' ;

MINUS
	: '-' ;

PLUS
	: '+' ;

GREATER
	: '>' ;

GREATEREQUAL
	: '>' '='
	| '\u2265' ;

RGUILLEMETS
	: '>' '>' ;

WS
	: (' '
  |   '\t'
  |   '\n'
  |   '\r' )
  -> channel(HIDDEN) ;

STRING_LITERAL
	: '"' ('\\' . | ~( '"' | '\\') )* '"' ;

/* LESS_DISPATCH
	: IMPLICIT_IDENT
	| EQV
	| LESSEQUAL
	| LGUILLEMETS
	| LESS ;
*/
LESS
	: '<' ;

LESSEQUAL
	: '<' '='
	| '\u2264' ;

LGUILLEMETS
	: '<' '<' ;

IMPLICIT_IDENT
	: '<' (LETTER)+ '>' ;

EQV
	: '<->'
	| '\u2194' ;

PRIMES_OR_CHARLITERAL
	: PRIMES
	| CHAR_LITERAL
	| PRIMES ;

fragment PRIMES
	: ('\'')+ ;

fragment CHAR_LITERAL
	: '\'' ((' '..'&')
	| ('('..'[')
	| (']'..'~')
	| ('\\' ('\'' | '\\' | 'n' | 'r' | 't' | 'b' | 'f' | '"'/* | 'u' HEX */ ))) '\'' ;

fragment QUOTED_STRING_LITERAL
	: '"' ('\\' . | '\n' | ~('\n' | '"' | '\\') )* '"' ;

SL_COMMENT
	: '//' (~('\n' | '\uFFFF'))* ('\n' | '\uFFFF' | EOF)
      -> skip //channel(HIDDEN)
    ;

ML_COMMENT
	: '/*' .*? '*/'
	  -> skip //channel(HIDDEN)
    ;

// A single Digit that is followed by a ( is an ident, otherwise it's a number

HEX_LITERAL
	: '0' 'x' (DIGIT | 'a'..'f' | 'A'..'F')+ ;

fragment DIGIT
	: '0'..'9' ;

fragment HEX
	: ('a'..'f'|'A'..'F'|DIGIT )
	  ('a'..'f'|'A'..'F'|DIGIT )
	  ('a'..'f'|'A'..'F'|DIGIT )
	  ('a'..'f'|'A'..'F'|DIGIT ) ;

fragment LETTER
	: 'a'..'z'
	| 'A'..'Z' ;

fragment IDCHAR
	: LETTER
	| DIGIT
	| '_'
	| '#'
	| '$' ;

IDENT
	: ( (LETTER | '_' | '#' | '$') (IDCHAR)*
) ;

NUM_LITERAL
	: (DIGIT)+ ;

