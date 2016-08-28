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

parser grammar KeYCommonRuleParser ;

options {
    tokenVocab = KeYCommonLexer ;
}

import KeYCommonParser;

rulename
        :
        IDENT
        ;        

taclet 
  :
  name=rulename 
  LBRACE
      ( ASSUMES LPAREN sequent RPAREN )?
        FIND LPAREN formulaTermOrSequent RPAREN
      ( applicationRestrictions )*      
      goalList
      ( ADDPROGVARS LPAREN simple_ident_comma_list RPAREN )?
      ( DISPLAYNAME displayname=STRING_LITERAL) ? 
      ( HELPTEXT helptext=STRING_LITERAL) ? 
      ( TRIGGER LBRACE triggerVariableDeclaration RBRACE (formula | term) AVOID formula )? 
  RBRACE
  ;

goalList
  :
  ( singleGoal ( SEMI singleGoal )* )?
  ;

singleGoal
  :
    ( label = STRING_LITERAL COLON )?
    ( REPLACEWITH LPAREN formulaTermOrSequent RPAREN )?
    ( ADD LPAREN formulaTermOrSequent RPAREN )?
    ( ADDRULES LPAREN taclet RPAREN )?    
  ;
  
triggerVariableDeclaration
    :
     logicalVariableDeclaration |
     schemaVariable=simple_ident  
    ;
  
applicationRestrictions
  :
     SAMEUPDATELEVEL | INSEQUENTSTATE | ANTECEDENTPOLARITY | SUCCEDENTPOLARITY | CLOSEGOAL
  ;  

formulaTermOrSequent
  :
     sequent | formula | term 
  ;
    
 sequent
  : 
    ( formula (COMMA formula)* )? SEQARROW ( formula (COMMA formula)* )?
  ;