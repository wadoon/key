// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
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

parser grammar KeYParser;

@members {
private SyntaxErrorReporter errorReporter = new SyntaxErrorReporter();
public SyntaxErrorReporter getErrorReporter() { return errorReporter;}
}

options { tokenVocab=KeYLexer; } // use tokens from STLexer.g4

file: (decls problem? proof?) EOF;

decls
:
    ( profile                // for problems
    | pref=preferences       // for problems
    | bootClassPath          // for problems
    | stlist=classPaths      // for problems
    | string=javaSource      // for problems
    | one_include_statement
    | options_choice
    | option_decls
    | sort_decls
    | prog_var_decls
    | schema_var_decls
    | pred_decls
    | func_decls
    | transform_decls
    | ruleset_decls
    | contracts             // for problems
    | invariants            // for problems
    | rulesOrAxioms         // for problems
    )*
;

problem
:
  ( PROBLEM LBRACE a=term RBRACE
  | CHOOSECONTRACT (chooseContract=string_value SEMI)?
  | PROOFOBLIGATION  (proofObligation=string_value SEMI)?
  )
  proofScript?
;



one_include_statement
:
    (INCLUDE | INCLUDELDTS)
    one_include (COMMA one_include)* SEMI
;

one_include 
:
    absfile=IDENT | relfile=string_value
;

options_choice
:
  WITHOPTIONS activated_choice (COMMA activated_choice)* SEMI
;

activated_choice
:
    cat=IDENT COLON choice_=IDENT
;

option_decls
:
    OPTIONSDECL LBRACE (choice SEMI)* RBRACE
;

choice
:
  category=IDENT
  (COLON LBRACE doc+=DOC_COMMENT? choice_option+=IDENT (COMMA doc+=DOC_COMMENT? choice_option+=IDENT)* RBRACE)?
;

sort_decls
:
 SORTS LBRACE (one_sort_decl)* RBRACE
;

one_sort_decl
:
      GENERIC  sortIds=simple_ident_dots_comma_list
        (ONEOF sortOneOf = oneof_sorts)?
        (EXTENDS sortExt = extends_sorts)? SEMI
    | PROXY  sortIds=simple_ident_dots_comma_list (EXTENDS sortExt=extends_sorts)? SEMI
    | ABSTRACT? sortIds=simple_ident_dots_comma_list (EXTENDS sortExt=extends_sorts)?  SEMI
;

simple_ident_dots
:
  simple_ident (DOT simple_ident )* | NUM_LITERAL
;

simple_ident_dots_comma_list
:
  simple_ident_dots (COMMA simple_ident_dots)*
;


extends_sorts
:
    sortId (COMMA sortId)*
;

oneof_sorts
:
    LBRACE
    s = sortId (COMMA s = sortId) *
    RBRACE
;

keyjavatype
:
    type = simple_ident_dots (EMPTYBRACKETS)*
;

prog_var_decls
:
    PROGRAMVARIABLES
    LBRACE
    (
        kjt = keyjavatype
        var_names = simple_ident_comma_list
        SEMI
    )*
    RBRACE
;

//this rule produces a StringLiteral
string_literal: id=STRING_LITERAL;

//this rule produces a String
string_value: STRING_LITERAL;

simple_ident
:
    id=IDENT
;

simple_ident_comma_list
:
    id = simple_ident (COMMA id = simple_ident )*
;


schema_var_decls :
    SCHEMAVARIABLES LBRACE
    ( one_schema_var_decl )*
    RBRACE
;

one_schema_var_decl
:
    (
           MODALOPERATOR one_schema_modal_op_decl
         | PROGRAM
            (schema_modifiers)?
            id = simple_ident
            (LBRACKET nameString=simple_ident EQUALS parameter=simple_ident_dots RBRACKET)?
            ids=simple_ident_comma_list
         | FORMULA
           (schema_modifiers)?
            ids = simple_ident_comma_list
         | TERMLABEL
           (schema_modifiers)?
           ids=simple_ident_comma_list
         | UPDATE
           (schema_modifiers)?
           ids=simple_ident_comma_list
         | SKOLEMFORMULA
           (schema_modifiers)?
           ids=simple_ident_comma_list
         | ( TERM
           | (VARIABLES | VARIABLE)
           | SKOLEMTERM
           )
           (schema_modifiers)?
           s=sortId
           ids=simple_ident_comma_list
    )
    SEMI
;

schema_modifiers
    :
        LBRACKET
        opts = simple_ident_comma_list
        RBRACKET
       
    ;

one_schema_modal_op_decl
:
    (LPAREN sort = sortId RPAREN)?
    LBRACE ids = simple_ident_comma_list RBRACE id = simple_ident
;

pred_decl
    :
        pred_name = funcpred_name

        (
	    whereToBind = where_to_bind
	)?
     argSorts = arg_sorts
        SEMI
    ;

pred_decls
    :
        PREDICATES
        LBRACE
        (
            pred_decl
        ) *
        RBRACE
    ;


location_ident
    :
        id = simple_ident
   
    ;



func_decl

    :
        (
            UNIQUE 
        )?

        retSort = sortId

        func_name = funcpred_name

	(
	    whereToBind = where_to_bind
	)?
        argSorts = arg_sorts
        SEMI
    ;

func_decls
    :
        FUNCTIONS
        LBRACE
        (
            func_decl
        ) *
        RBRACE
    ;


// like arg_sorts but admits also the keyword "\formula"
arg_sorts_or_formula
:
    ( LPAREN
      arg_sorts_or_formula_helper
      (COMMA arg_sorts_or_formula_helper)*
      RPAREN
    )?
;

arg_sorts_or_formula_helper
:
    sortId | FORMULA
;

transform_decl
    :
        (
          retSort = sortId
        | FORMULA 
        )

        trans_name = funcpred_name
        argSorts = arg_sorts_or_formula
        SEMI
    ;

transform_decls
    :
        TRANSFORMERS
        LBRACE
        (
            transform_decl
        ) *
        RBRACE
    ;

arrayopid

    :
        EMPTYBRACKETS
        LPAREN
        componentType = keyjavatype
        RPAREN
    ;

arg_sorts

    :
        (
            LPAREN
            s = sortId 
            (
                COMMA s = sortId 
            ) *
            RPAREN
        ) ?
        
    ;

where_to_bind

    :
        LBRACE
        b+=(TRUE | FALSE)
        (COMMA b+=(TRUE | FALSE) )*
        RBRACE
        
   ;

ruleset_decls
    :
        HEURISTICSDECL
        LBRACE
        (id = simple_ident SEMI)*
        RBRACE
    ;

sortId
:
    id=simple_ident_dots (EMPTYBRACKETS)*
;

id_declaration
:
  id=IDENT ( COLON s=sortId ) ?
;

funcpred_name
:
    (sortId DOUBLECOLON)? name=simple_ident_dots
;


/**
 * In the special but important case of Taclets, we don't yet know
 * whether we are going to have a term or a formula, and it is hard
 * to decide a priori what we are looking at.  So the `term'
 * non-terminal will recognize a term or a formula.  The `formula'
 * reads a formula/term and throws an error if it wasn't a formula.
 * This gives a rather late error message. */
//region terms and formulas

termEOF: term EOF; // toplevel

boolean_literal: TRUE | FALSE;
literals:
    boolean_literal
  | char_literal
  | number
  | string_literal
;

term
:
  literals                    #termLiterals
  | accessterm                #termAccess
  | AT name=simple_ident      #abbreviation
  | LPAREN term RPAREN        #termParen
  | ifThenElseTerm            #termIfThenElse
  | ifExThenElseTerm          #termIfExThenElse
  | NOT term                  #negation
  | MINUS term                #unaryMinus
  | LPAREN sort=sortId RPAREN term #cast
  | location_term             #termLocation
  | substitutionterm          #termSubstitution
  | updateterm                #termUpdate
  | MODALITY term             #termModality
  |<assoc=right>
    term (SLASH | PERCENT) term #termDivisionModulo
  |	term STAR term            #termMult
  | term (PLUS|MINUS) term    #termWeakArith
  | term ( LESS | LESSEQUAL | GREATER |  GREATEREQUAL ) term #termCompare
  | term NOT_EQUALS term      #termNotEquals
  | term EQUALS term          #termEquals
  | term AND term             #conjunction_term
  | term OR term              #disjunction_term
  | term IMP term             #implication_term
  | term EQV term             #equivalence_term
  | term ASSIGN term          #elementary_update_term
  | term PARALLEL term        #parallel
  | term (LGUILLEMETS labels = label RGUILLEMETS)
                              #termLabeled
;

accessterm
:
  varfuncid=funcpred_name
  ( (LBRACE boundVars=bound_variables RBRACE)?
    args=argument_list
  )?
  atom_suffix*
  heap_suffix?
;

heap_suffix: AT term;

atom_suffix
:
      accessterm_bracket_suffix
    | attribute_or_query_suffix
;

accessterm_bracket_suffix
:
    LBRACKET
    ( target=term ASSIGN val=term // heap assignment
    | id=simple_ident args=argument_list // for heap terms, this could be ambigous with logicTermReEntry
    | STAR
    | indexTerm=term (DOTRANGE rangeTo=term)? //array or sequence access
    )
    RBRACKET
;


static_query
:
    queryRef=staticAttributeOrQueryReference
    args=argument_list
;


label
:
   l=single_label  (COMMA l=single_label )*
;

single_label
:
  (name=IDENT
  | star=STAR  )

  (LPAREN
    (string_value
      (COMMA string_value )*
    )?
    RPAREN
  )?
;


location_term
:
    LPAREN obj=term COMMA field=term RPAREN
;

substitutionterm
:
   LBRACE SUBST
   bv=one_bound_variable
   SEMI
   replacement=term
   RBRACE
   haystack=term
;

updateterm
:
  LBRACE term RBRACE term
;

staticAttributeOrQueryReference
:
  id=IDENT
  (EMPTYBRACKETS )*
;

static_attribute_suffix
:
  attributeName = staticAttributeOrQueryReference
;


attribute_or_query_suffix
:
    DOT ( STAR 
        | ( memberName=attrid
            (result=query_suffix )?
          ) 
        )
;
 
attrid
:
// the o.f@(packagename.Classname) syntax has been dropped.
// instead, one can write o.(packagename.Classname::f)
    id = simple_ident
  | LPAREN clss = sortId DOUBLECOLON id2 = simple_ident RPAREN
;

query_suffix 
:
    args = argument_list
;
 


ifThenElseTerm
:
  IF LPAREN condF = term RPAREN
  THEN LPAREN thenT = term RPAREN
  ELSE LPAREN elseT = term RPAREN
;
 


ifExThenElseTerm
:
  IFEX exVars = bound_variables
  LPAREN condF = term RPAREN
  THEN LPAREN thenT = term RPAREN
  ELSE LPAREN elseT = term RPAREN
;

quantifierterm
:
  (FORALL | EXISTS)
  bound_variables term
;

locset_term
:
    LBRACE
        ( l = location_term 
        ( COMMA l = location_term  )* )?
    RBRACE
;


bound_variables
:
    var=one_bound_variable (COMMA var=one_bound_variable)* SEMI
;

one_bound_variable 
:
  s=sortId? id=simple_ident
;

argument_list
:
    LPAREN
    (term (COMMA term)*)?
    RPAREN
;

number:
  (MINUS )?
  ( NUM_LITERAL | HEX_LITERAL | BIN_LITERAL)
;

char_literal:
    CHAR_LITERAL;


varId: id=IDENT;
varIds: ids=simple_ident_comma_list;

triggers
:
  TRIGGER
  LBRACE id=simple_ident RBRACE
  t=term
    (AVOID avoidCond+=term
      (COMMA avoidCond+=term )*)?
  SEMI
;

taclet
:
  (LEMMA )?
  name=IDENT (choices_=option_list)?
  LBRACE
  ( form=term
  |
    ( SCHEMAVAR one_schema_var_decl ) *
    ( ASSUMES LPAREN ifSeq=seq RPAREN ) ?
    ( FIND LPAREN find=termorseq RPAREN
        (   SAMEUPDATELEVEL
          | INSEQUENTSTATE
          | ANTECEDENTPOLARITY
          | SUCCEDENTPOLARITY
        )*
    )?

    ( VARCOND LPAREN varexplist RPAREN ) ?
    goalspecs
    modifiers
  )
  RBRACE
;

modifiers
:
  ( rs = rulesets
  | NONINTERACTIVE
  | DISPLAYNAME dname = string_value
  | HELPTEXT htext = string_value
  | triggers
  ) *
;

seq: ant=semisequent SEQARROW suc=semisequent;

seqEOF: seq EOF;

termorseq
:
      head=term (COMMA s=seq | SEQARROW ss=semisequent) ?
    | SEQARROW ss=semisequent
;

semisequent
:
    /* empty */
  | head=term ( COMMA ss=semisequent) ?
;

varexplist : varexp (COMMA varexp)* ;

varexpId:
    APPLY_UPDATE_ON_RIGID
  | SAME_OBSERVER
  | DROP_EFFECTLESS_ELEMENTARIES
  | DROP_EFFECTLESS_STORES
  | DIFFERENTFIELDS
  | SIMPLIFY_IF_THEN_ELSE_UPDATE
  | CONTAINS_ASSIGNMENT
  | ISENUMTYPE
  | ISTHISREFERENCE
  | STATICMETHODREFERENCE
  | ISREFERENCEARRAY
  | ISARRAY
  | ISARRAYLENGTH
  | IS_ABSTRACT_OR_INTERFACE
  | ENUM_CONST
  | FINAL
  | STATIC
  | ISLOCALVARIABLE
  | ISOBSERVER
  | DIFFERENT
  | METADISJOINT
  | EQUAL_UNIQUE
  | FREELABELIN
  | ISCONSTANT
  | HASLABEL
  | ISSTATICFIELD
  | HASSUBFORMULAS
  | FIELDTYPE
  | NEW
  | NEW_TYPE_OF
  | NEW_DEPENDING_ON
  | HAS_ELEMENTARY_SORT
  | SAME
  | ISSUBTYPE
  | STRICT ISSUBTYPE
  | DISJOINTMODULONULL
  | NOTFREEIN
  | HASSORT
  | NEWLABEL
  | ISREFERENCE
  | MAXEXPANDMETHOD
;


// ELEMSORT flag for hassort

varexp_argument
:
    sortId //also covers possible varId
  | TYPEOF LPAREN y=varId RPAREN
  | CONTAINERTYPE LPAREN y=varId RPAREN
  | DEPENDINGON LPAREN y=varId RPAREN
;

varexp
:
  negate=NOT_?
  varexpId
  (LBRACKET IDENT RBRACKET)?
  LPAREN varexp_argument (COMMA varexp_argument)* RPAREN
;

goalspecs:
      CLOSEGOAL
    | goalspecwithoption (SEMI goalspecwithoption)*
;

goalspecwithoption
 :
    soc=option_list LBRACE goalspec RBRACE
  | goalspec
;

option
:
  cat=IDENT COLON value=IDENT
;

option_list
:
  LPAREN
    option (COMMA option)*
  RPAREN
;

goalspec
:
  (name=string_value COLON)?
  ( rwObj = replacewith
    addSeq=add?
    addRList=addrules?
    addpv=addprogvar?
  | addSeq=add (addRList=addrules)?
  | addRList=addrules
  )
;

replacewith:  REPLACEWITH LPAREN o=termorseq RPAREN;
add:          ADD LPAREN s=seq RPAREN;
addrules:     ADDRULES LPAREN lor=tacletlist RPAREN;
addprogvar:   ADDPROGVARS LPAREN pvs=pvset RPAREN;
tacletlist:   taclet (COMMA taclet)*;

pvset: varId (COMMA varId)*;

rulesets:
  HEURISTICS LPAREN ruleset
  (COMMA ruleset) * RPAREN
;

ruleset: id=IDENT;

metaId:  id=simple_ident ;

metaTerm:
    vf=metaId (LPAREN t+=term (COMMA t+=term)* RPAREN)?
;


contracts
:
   CONTRACTS
   LBRACE
   (one_contract)*
   RBRACE
;

invariants
:
   INVARIANTS LPAREN selfVar=one_bound_variable RPAREN
   LBRACE
   (one_invariant)*
   RBRACE
;

one_contract
:
   contractName = simple_ident LBRACE
   (prog_var_decls)?
   fma=term MODIFIES modifiesClause=term
   RBRACE SEMI
;

one_invariant
:
     invName = simple_ident LBRACE
     fma=term
     (DISPLAYNAME displayName=string_value)?
     RBRACE SEMI
;

rulesOrAxioms:
    (RULES|AXIOMS)
    (choices = option_list)?
    (LBRACE (s=taclet SEMI)* RBRACE)
;

bootClassPath
:
  BOOTCLASSPATH id=string_value SEMI
;

classPaths
:
  CLASSPATH s=string_value (COMMA s=string_value)* SEMI
;

javaSource: JAVASOURCE result=oneJavaSource SEMI;

oneJavaSource
:
  ( string_value
  | COLON
  )+ 
;

profile: PROFILE name=string_value SEMI;

preferences
:
	KEYSETTINGS LBRACE (s=string_value)? RBRACE
;

proofScript
:
  PROOFSCRIPT ps = STRING_LITERAL
;

proof: PROOF EOF;
// Parsing ends at PROOF token, rest is handled on the lexer level
//proofBody;

/*proofBody
:
  LBRACE
      ( pseudosexpr )+
  RBRACE
;

pseudosexpr
:
  LPAREN
    (proofElementId=expreid
      (str=string_literal)?
      (pseudosexpr)*
    )?
  RPAREN
;

expreid: id=simple_ident;

/*

formula
    :
      NOT formula  #negatedFormula
    | programFml   #programFormula
    | LBRACE SUBST logicalVariableDeclaration SEMI replacement=term RBRACE in=formula  #substitutionFormula
    | LBRACE parallelUpdate RBRACE formula                                             #updateFormula
    | IF LPAREN condition=formula RPAREN THEN LPAREN thenFml=formula RPAREN ELSE LPAREN elseFml=formula RPAREN #ifThenElseFormula
    | quantifier=(FORALL | EXISTS) logicalVariableDeclaration SEMI formula #quantifiedFormula
    | formula AND formula  #conjunctiveFormula
    | formula OR formula   #disjunctiveFormula
    |<assoc=right> formula IMP formula  #implicationFormula
    | formula EQV formula  #equivalenceFormula
    | term op=(LESS | LESSEQUAL | EQUALS | NOT_EQUALS | GREATER | GREATEREQUAL) term #comparisonFormula
    | sym=funcpred_name arguments? #predicateFormula
    | LPAREN formula RPAREN        #parenthesizedFormula
    ;

programFml
   :
       BOX_BEGIN BOX_END formula
     | DIAMOND_BEGIN  DIAMOND_END formula
     | MODALITY_BEGIN MODALITY_END formula
   ;

logicalVariableDeclaration
    :
    sort_name simple_ident
    ;

term
    :
      MINUS term  #unaryMinusTerm
    | LBRACE SUBST logicalVariableDeclaration SEMI replacement=term RBRACE in=term                       #substitutionTerm
    | LBRACE parallelUpdate RBRACE term                                                                  #updateTerm
    | IF LPAREN condition=formula RPAREN THEN LPAREN thenTrm=term RPAREN ELSE LPAREN elseTrm=term RPAREN #ifThenElseTerm
    | term op=(STAR | SLASH) term   #mulDivTerm
    | term op=(PLUS | MINUS) term   #addSubTerm
    | literal=digit                 #numberLiteralTerm
    | sym=funcpred_name arguments?  #functionTerm
    | funcpred_name (DOT funcpred_name)+ (AT funcpred_name)?   #attributeTerm
    | funcpred_name (LBRACKET elementaryUpdate RBRACKET)+      #heapStoreTerm
    | LPAREN term RPAREN                                       #parenthesizedTerm
    ;

arguments
    :
      LPAREN argumentList? RPAREN
    ;

argumentList
   :
     term (COMMA term)*
   ;

parallelUpdate
   :
     update (PARALLEL parallelUpdate)*
   ;

update
   :
     elementaryUpdate
   | updateOnUpdateApplication
   | LPAREN parallelUpdate RPAREN
   ;

elementaryUpdate
   :
     loc=simple_ident ASSIGN value=term
   ;

updateOnUpdateApplication
   :
    LBRACE update RBRACE update
   ;
 */