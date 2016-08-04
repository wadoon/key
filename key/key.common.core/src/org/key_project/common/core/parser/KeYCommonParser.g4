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

parser grammar KeYCommonParser ;

@parser::header {
    package org.key_project.common.core.parser;
}

options {
    tokenVocab = KeYCommonLexer ;
}

import KeYCommonDeclarationParser;

formula 
    : 
      NOT formula  #negatedFormula
    | LBRACE SUBST logicalVariableDecl SEMI term RBRACE formula     #substitutionFormula
    | LBRACE parallelUpdate RBRACE formula                                  #updateFormula
    | quantifier=(FORALL | EXISTS) logicalVariableDecl SEMI formula #quantifiedFormula
    | formula AND formula  #conjunctiveFormula 
    | formula OR formula   #disjunctiveFormula
    | formula IMP formula  #implicationFormula
    | formula EQV formula  #equivalenceFormula
    | term op=(LESS | LESSEQUAL | EQUALS | NOT_EQUALS | GREATER | GREATEREQUAL) term #comparisonFormula 
    | sym=funcpred_name arguments? #predicateFormula
    | LPAREN formula RPAREN #parenthesizedFormula
    ;

logicalVariableDecl
    :
    sort_name simple_ident  
    ;

term
    : 
      MINUS term                      #unaryMinusTerm
    | LBRACE SUBST logicalVariableDecl SEMI term RBRACE term #substitutionTerm
    | LBRACE parallelUpdate RBRACE term       #updateTerm
    | term op=(STAR | SLASH) term     #mulDivTerm
    | term op=(PLUS | MINUS) term     #addSubTerm
    | sym=funcpred_name arguments?    #functionTerm
    | funcpred_name (DOT funcpred_name)+ (AT funcpred_name)? #attributeTerm
    | funcpred_name (LBRACKET term | (simple_ident ASSIGN term RBRACKET))+ #heapStoreTerm
    | LPAREN term RPAREN              #parenthesizedTerm
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
     LBRACE update RBRACE update   #updateOnUpdateApplication
   | loc=simple_ident ASSIGN term  #elementaryUpdate
   | LPAREN parallelUpdate RPAREN  #parenthesizedUpdate
   ;

