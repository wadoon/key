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
      ( SCHEMAVAR one_schema_var_decl )*  
      ( ASSUMES LPAREN sequent RPAREN )?
      ( FIND LPAREN formulaTermOrSequent RPAREN )?
      ( applicationRestrictions )*      
      ( VARCOND LPAREN variablecondition (COMMA variablecondition)* RPAREN )?
      goalList
      ( ADDPROGVARS LPAREN simple_ident_comma_list RPAREN )?
      (   ( HEURISTICS LPAREN IDENT (COMMA IDENT)* RPAREN )
        | ( TRIGGER LBRACE triggerVariableDeclaration RBRACE (formula | term) (AVOID formula (COMMA formula)*)? )
        | ( DISPLAYNAME displayname=STRING_LITERAL )
        | ( HELPTEXT helptext=STRING_LITERAL )         
      )*
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
    
logicalVariableDeclaration  // overrides inherited rule; local variable should not be declared (use \schemaVar \variable T x; and use x in quantifiers, subst etc.)
  :
     schemaVariable=simple_ident 
  ;    
    
 sequent
  : 
    ( formula (COMMA formula)* )? SEQARROW ( formula (COMMA formula)* )?
  ;
  
 variablecondition
  :
    NOT_? condition=varcondKind LPAREN varcondExpr (COMMA varcondExpr)* RPAREN    
  ;
  
varcondKind
  :
     KEYWORD_IDENT
  ;
  
varcondExpr
  :
       KEYWORD_IDENT LPAREN varcondExpr (COMMA varcondExpr)* RPAREN 
     | formula | term
  ;  
  