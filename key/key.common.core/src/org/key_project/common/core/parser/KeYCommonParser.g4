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
    | formula AND formula  #conjunctiveFormula 
    | formula OR formula   #disjunctiveFormula
    | formula IMP formula  #implicationFormula
    | formula EQV formula  #equivalenceFormula                                       
    | term op=(LESS | LESSEQUAL | EQUALS | NOT_EQUALS | GREATER | GREATEREQUAL) term #comparisonFormula 
    | sym=funcpred_name ( LPAREN term (COMMA term)* RPAREN )? #predicateFormula
    | LPAREN formula RPAREN #parenthesizedFormula
    ;

term 
    : 
      MINUS term                  # unaryMinusTerm
    | term op=(PLUS | MINUS) term # addSubTerm 
    | term op=(STAR | SLASH) term # mulDivTerm
    | sym = funcpred_name (LPAREN term (COMMA term)* RPAREN)?  # functionTerm
    ;
