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

@header {
    package org.key_project.common.core.parser;
}

options {
    tokenVocab = KeYCommonLexer ;
}

/*
decls
	: ( one_include_statement )*
	  ( options_choice )?
      (   option_decls
        | sort_decls
        | prog_var_decls
        | schema_var_decls
        | pred_decls
        | func_decls
        | transform_decls
        | ruleset_decls
      ) * ;
*/

// This is a simplified version of the top-level declaration:
// Only sorts, predicates and functions (sufficient for integerHeader.key).
decls
    : (   sort_decls
        | pred_decls
        | func_decls
      ) *
    ;

sort_decls
    : SORTS
      LBRACE
      ( multipleSorts = one_sort_decl )*
      RBRACE
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

func_decls
    : FUNCTIONS
      LBRACE
      ( func_decl ) *
      RBRACE
    ;

one_sort_decl
    : (   GENERIC sortIds = simple_ident_comma_list
          ( ONEOF sortOneOf = oneof_sorts )?
          ( EXTENDS sortExt = extends_sorts )?
        | PROXY sortIds = simple_ident_comma_list
          ( EXTENDS sortExt = extends_sorts )?
        | (ABSTRACT )?
          firstSort = simple_ident_dots
          (   (EXTENDS sortExt = extends_sorts )
            | ((COMMA) sortIds = simple_ident_comma_list )
          )?
      ) SEMI
    ;

pred_decl
   : pred_name = funcpred_name
     (
       whereToBind = where_to_bind
     )?
     argSorts = arg_sorts
     SEMI
   ;

func_decl
    : ( UNIQUE )?
      retSort = sort_name
      func_name = funcpred_name
      ( whereToBind = where_to_bind )?
      argSorts = arg_sorts
      SEMI
    ;

extends_sorts
    : s = simple_ident_dots
      (
        COMMA s = simple_ident_dots
      ) *
    ;

oneof_sorts
    : LBRACE
      s = sortId
      (
        COMMA s = sortId
      ) *
      RBRACE
    ;

// like arg_sorts but admits also the keyword "\formula"
arg_sorts_or_formula
    : (   LPAREN
          (   s = sortId
            | FORMULA
          )
          (
            COMMA
            (   s = sortId
              | FORMULA
            )
          ) *
          RPAREN
      ) ?
    ;

arg_sorts
    : (  LPAREN
         s = sortId
         ( COMMA s = sortId ) *
         RPAREN
      ) ?
    ;

where_to_bind
    :
        LBRACE
        (
            TRUE | FALSE
        )
        (
           COMMA
           (
               TRUE | FALSE
           )
        )*
        RBRACE
   ;

funcpred_name
    : (
        prefix = sort_name
        DOUBLECOLON
        name = simple_ident
      )                      # GenericFunctionName
    | name = simple_ident    # SimpleIdentFunctionName
    // The following case is addressing the declaration of the
    // single-digit "numbers" functions 0-9.
    | name = digit           # DigitFunctionName
    ;

digit : DIGIT_DISPATCH ;

sortId
    : s = simple_ident_dots
    ;

sort_name
    : name = simple_ident_dots
      ( brackets = EMPTYBRACKETS )*
    ;

simple_ident_dots
    : id = simple_ident
      (  DOT
         (   id = simple_ident
           | num = NUM_LITERAL
         )
      )*
 ;

simple_ident_comma_list
   : id = simple_ident
     (COMMA id = simple_ident )*
   ;

simple_ident
   : id = IDENT
   ;
