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
      // TODO: add local schema variable conditions here
  
      ( ASSUMES LPAREN sequent RPAREN )?
        FIND LPAREN formulaTermOrSequent RPAREN
      ( applicationRestrictions )*      
      // TODO: add variable conditions here
      //    - allow names of conditions to start with backslash (for backward compatibility)
      //      but use a token BACKSLASHALLOWEDIDENT or similar
      //      hence cond. do not need to be backslahed and we do not need lexer keywords 
      goalList
      ( ADDPROGVARS LPAREN simple_ident_comma_list RPAREN )?
      ( DISPLAYNAME displayname=STRING_LITERAL) ? 
      ( HELPTEXT helptext=STRING_LITERAL) ? 
      ( TRIGGER LBRACE triggerVariableDeclaration RBRACE (formula | term) AVOID formula )? 
  RBRACE
  ;

goalList
  :
    singleGoal ( SEMI singleGoal )*
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