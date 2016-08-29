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
// Copyright (C) 2012-2016 Universitaet Karlsruhe, Germany
//                         Technische Universität Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

parser grammar KeYCommonParser ;

options {
    tokenVocab = KeYCommonLexer ;
}

import KeYCommonDeclarationParser;

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
 