/*
 [The "BSD licence"]
 Copyright (c) 2013 Terence Parr, Sam Harwell
 Copyright (c) 2017 Ivan Kochurkin (upgrade to Java 8)
 All rights reserved.

 Redistribution and use in source and binary forms, with or without
 modification, are permitted provided that the following conditions
 are met:
 1. Redistributions of source code must retain the above copyright
    notice, this list of conditions and the following disclaimer.
 2. Redistributions in binary form must reproduce the above copyright
    notice, this list of conditions and the following disclaimer in the
    documentation and/or other materials provided with the distribution.
 3. The name of the author may not be used to endorse or promote products
    derived from this software without specific prior written permission.

 THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

grammar JavaK;

@parser::members {
  /** allow special key-java constructs */
  boolean keyMode = true;
  /** allow special key-java constructs */
  boolean schemeMode = true;
}

@lexer::members {
  public java.util.List<Token> docs = new java.util.ArrayList<>(1024);
@Override
	public Token nextToken() {
		Token tok = super.nextToken();
		if (tok.getType() == JavaKLexer.COMMENT || tok.getType() == JavaKLexer.LINE_COMMENT) {
			docs.add(tok);
		}
		return tok;
	}

}

compilationUnit
    : packageDeclaration? importDeclaration* typeDeclaration* EOF
    ;

packageDeclaration
    : annotation* PACKAGE qualifiedName ';'
    ;

importDeclaration
    : IMPORT STATIC? qualifiedName ('.' MUL)? ';'
    ;

typeDeclaration
    : classOrInterfaceModifier*
      (classDeclaration | enumDeclaration | interfaceDeclaration | annotationTypeDeclaration)
    | ';'
    ;

modifier
    : classOrInterfaceModifier
    | NATIVE
    | SYNCHRONIZED
    | TRANSIENT
    | VOLATILE
    ;

classOrInterfaceModifier
    : annotation
    | PUBLIC
    | PROTECTED
    | PRIVATE
    | STATIC
    | ABSTRACT
    | FINAL    // FINAL for class only -- does not apply to interfaces
    | STRICTFP
    ;

variableModifier
    : FINAL
    | annotation
    ;

classDeclaration
    : CLASS identifier typeParameters?
      (EXTENDS typeType)?
      (IMPLEMENTS typeList)?
      classBody
    ;

typeParameters
    : '<' typeParameter (',' typeParameter)* '>'
    ;

typeParameter
    : annotation* identifier (EXTENDS typeBound)?
    ;

typeBound
    : typeType ('&' typeType)*
    ;

enumDeclaration
    : ENUM identifier (IMPLEMENTS typeList)? '{' enumConstants? ','? enumBodyDeclarations? '}'
    ;

enumConstants
    : enumConstant (',' enumConstant)*
    ;

enumConstant
    : annotation* identifier arguments? classBody?
    ;

enumBodyDeclarations
    : ';' classBodyDeclaration*
    ;

interfaceDeclaration
    : INTERFACE identifier typeParameters? (EXTENDS typeList)? interfaceBody
    ;

classBody
    : '{' classBodyDeclaration* '}'
    ;

interfaceBody
    : '{' interfaceBodyDeclaration* '}'
    ;

classBodyDeclaration
    : ';'
    | STATIC? block
    | modifier* memberDeclaration
    ;

memberDeclaration
    : methodDeclaration
    | genericMethodDeclaration
    | fieldDeclaration
    | constructorDeclaration
    | genericConstructorDeclaration
    | interfaceDeclaration
    | annotationTypeDeclaration
    | classDeclaration
    | enumDeclaration
    ;

/* We use rule this even for void methods which cannot have [] after parameters.
   This simplifies grammar and we can consider void to be a type, which
   renders the [] matching as a context-sensitive issue or a semantic check
   for invalid return type after parsing.
 */
methodDeclaration
    : typeTypeOrVoid identifier formalParameters (LBRACK RBRACK)*
      (THROWS qualifiedNameList)?
      methodBody
    ;

methodBody
    : block
    | ';'
    ;

typeTypeOrVoid
    : typeType
    | VOID
    ;

genericMethodDeclaration
    : typeParameters methodDeclaration
    ;

genericConstructorDeclaration
    : typeParameters constructorDeclaration
    ;

constructorDeclaration
    : identifier formalParameters (THROWS qualifiedNameList)? (constructorBody=block|';')//allow only decls w/o implementation
    ;

fieldDeclaration
    : typeType variableDeclarators ';'
    ;

interfaceBodyDeclaration
    : modifier* interfaceMemberDeclaration
    | ';'
    ;

interfaceMemberDeclaration
    : constDeclaration
    | interfaceMethodDeclaration
    | genericInterfaceMethodDeclaration
    | interfaceDeclaration
    | annotationTypeDeclaration
    | classDeclaration
    | enumDeclaration
    ;

constDeclaration
    : typeType constantDeclarator (',' constantDeclarator)* ';'
    ;

constantDeclarator
    : identifier (LBRACK RBRACK)* '=' variableInitializer
    ;

// see matching of [] comment in methodDeclaratorRest
// methodBody from Java8
interfaceMethodDeclaration
    : interfaceMethodModifier* (typeTypeOrVoid | typeParameters annotation* typeTypeOrVoid)
      identifier formalParameters ('[' ']')* (THROWS qualifiedNameList)? methodBody
    ;

// Java8
interfaceMethodModifier
    : annotation
    | PUBLIC
    | ABSTRACT
    | DEFAULT
    | STATIC
    | STRICTFP
    ;

genericInterfaceMethodDeclaration
    : typeParameters interfaceMethodDeclaration
    ;

variableDeclarators
    : variableDeclarator (',' variableDeclarator)*
    ;

variableDeclarator
    : variableDeclaratorId ('=' variableInitializer)?
    ;

variableDeclaratorId
    : identifier (LBRACK RBRACK)*
    ;

variableInitializer
    : arrayInitializer
    | expression
    ;

arrayInitializer
    : '{' (variableInitializer (',' variableInitializer)* (',')? )? '}'
    ;

classOrInterfaceType
    : identifier typeArguments? ('.' identifier typeArguments?)*
    ;

typeArgument
    : typeType
    | QUESTION ((EXTENDS | SUPER) typeType)?
    ;

qualifiedNameList
    : qualifiedName (',' qualifiedName)*
    ;

formalParameters
    : '(' formalParameterList? ')'
    ;

formalParameterList
    : formalParameter (',' formalParameter)* (',' lastFormalParameter)?
    | lastFormalParameter
    ;

formalParameter
    : variableModifier* typeType variableDeclaratorId
    ;

lastFormalParameter
    : variableModifier* typeType '...' variableDeclaratorId
    ;

qualifiedName
    : identifier ('.' identifier)*
    ;

literal
    : integerLiteral
    | floatLiteral
    | CHAR_LITERAL
    | STRING_LITERAL
    | BOOL_LITERAL
    | NULL_LITERAL
    | TEXT_BLOCK
    | EMPTYMAPLITERAL
    | EMPTYSEQLITERAL
    | EMPTYSETLITERAL
    | {schemeMode}?
      isStaticSV
    | {schemeMode}?
      isStaticEvaluateSV
    ;

isStaticEvaluateSV
    : | '#static-evaluate' '(' e=expression /*checked for intanceOf*/ ')'
    ;
     /*        	{  result = factory.createRKeYMetaConstructExpression();
             	   ((RKeYMetaConstructExpression)result).setChild((Operator)e);
             	   ((RKeYMetaConstructExpression)result).setName("#static-evaluate");
             	}*/

isStaticSV:  ISSTATIC '(' expression ')';
/*{
    RKeYMetaConstructExpression result;
    Expression e;
}
{*/
/*     { result = factory.createRKeYMetaConstructExpression();
       ((RKeYMetaConstructExpression)result).setChild(e);
       ((RKeYMetaConstructExpression)result).setName("#isstatic");
       return result;
     }
*/



integerLiteral
    : DECIMAL_LITERAL
    | HEX_LITERAL
    | OCT_LITERAL
    | BINARY_LITERAL
    ;

floatLiteral
    : FLOAT_LITERAL
    | HEX_FLOAT_LITERAL
    ;

// ANNOTATIONS
altAnnotationQualifiedName
    : (identifier DOT)* '@' identifier
    ;

annotation
    : ('@' qualifiedName | altAnnotationQualifiedName) ('(' ( elementValuePairs | elementValue )? ')')?
    ;

elementValuePairs
    : elementValuePair (',' elementValuePair)*
    ;

elementValuePair
    : identifier '=' elementValue
    ;

elementValue
    : expression
    | annotation
    | elementValueArrayInitializer
    ;

elementValueArrayInitializer
    : '{' (elementValue (',' elementValue)*)? (',')? '}'
    ;

annotationTypeDeclaration
    : '@' INTERFACE identifier annotationTypeBody
    ;

annotationTypeBody
    : '{' (annotationTypeElementDeclaration)* '}'
    ;

annotationTypeElementDeclaration
    : modifier* annotationTypeElementRest
    | ';' // this is not allowed by the grammar, but apparently allowed by the actual compiler
    ;

annotationTypeElementRest
    : typeType annotationMethodOrConstantRest ';'
    | classDeclaration ';'?
    | interfaceDeclaration ';'?
    | enumDeclaration ';'?
    | annotationTypeDeclaration ';'?
    ;

annotationMethodOrConstantRest
    : annotationMethodRest
    | annotationConstantRest
    ;

annotationMethodRest
    : identifier '(' ')' defaultValue?
    ;

annotationConstantRest
    : variableDeclarators
    ;

defaultValue
    : DEFAULT elementValue
    ;

// STATEMENTS / BLOCKS

block
    : '{' blockStatement* '}'
    ;

blockStatement
    : localVariableDeclaration ';'
    | statement
    | localTypeDeclaration
    ;

localVariableDeclaration
    : variableModifier* typeType variableDeclarators
    ;

localTypeDeclaration
    : classOrInterfaceModifier*
      (classDeclaration | interfaceDeclaration)
    | ';'
    ;

throwStatement: THROW expression ';';

statement
    : block
    | assertStatement
    | ifStatement
    | forStatement
    | whileStatement
    | doWhileStatement
    | tryStatement
    | tryWithResourceStatement
    | switchStatement
    | synchronizedStatement
    | returnStatement
    | throwStatement
    | breakStatement
    | continueStatement
    | emptyStatement
    | statementExpression
    | labeledStatement
    | // java 12+
      yieldStatement
    | {keyMode}?    keyStatements
    /* key scheme mode */
    | {schemeMode}? schemeStatements
;

assertStatement: ASSERT expression (':' expression)? ';';
ifStatement: IF parExpression then=statement (ELSE otherwise=statement)?;
forStatement: FOR '(' forControl ')' statement;
whileStatement: WHILE parExpression statement;
doWhileStatement: DO statement WHILE parExpression ';';
tryStatement: TRY block (catchClause+ finallyBlock? | finallyBlock);
tryWithResourceStatement: TRY resourceSpecification block catchClause* finallyBlock?;
switchStatement: SWITCH parExpression '{' (switchRule+ | switchBlockStatementGroup* switchLabel*) '}';
synchronizedStatement: SYNCHRONIZED parExpression block;
returnStatement: RETURN expression? ';';
breakStatement: BREAK identifier? ';';
continueStatement: CONTINUE identifier? ';';
emptyStatement: SEMI;
statementExpression: expression ';';
labeledStatement: identifier ':' statement;
// java 12+
yieldStatement: YIELD expression ';';


/** key statements */
keyStatements
    : methodBodyStatement
    | methodCallStatement
    | loopScope
    | mergePointStatement
    | catchAllStatement
    | execStatement
    | transactionStatement
    ;

/** key statements */
methodCallStatement
    : METHODFRAME LPAREN ( 'result->' qn=identifier COMMA)? ec=executionContext RPAREN COLON block
    ;
methodBodyStatement
    : METHODFRAME LPAREN (qn=identifier ASSIGN)? tmp=expression AT bodySource=typeType RPAREN COLON block
    ;

loopScope: LOOPSCOPE LPAREN  expression RPAREN block;
mergePointStatement: MERGE_POINT LPAREN expression RPAREN SEMI;
catchAllStatement: '#catchAll' LPAREN qn=identifier RPAREN block;
execStatement: 'exec' block ccatchBlock*;
transactionStatement: (TRANSACTIONBEGIN | TRANSACTIONCOMMIT | TRANSACTIONFINISH | TRANSACTIONABORT) SEMI;


schemeStatements
    : rMethodCallStatement
    //TODO | rMethodBodyStatement
    | keYMetaConstructStatement
    | statementSV
    ;

/* VariableSpecification SVVariableDeclarator(boolean isForField) :
   {
       Identifier id;
       int dim = 0;
       Expression init = null;
       VariableSpecification result;
   }
   {
       ((id = VariableDeclaratorId() { dim = tmpDimension; })
        |(id = VariableSV()  {dim = tmpDimension; }))

   	[ "=" (init = VariableInitializer())
   	|(init = ExpressionSV())
   	]
   	{
   	    if (isForField) {
   		System.err.println("FIELD DECL WITH SV NOT SUPPORTED");
   		result=null;
   	    } else {
   		result = factory.createVariableSpecification(id, dim, init); //!!CHANGE
   	    }
   	    //    setPrefixInfo(result); // only after "=" !!!!!!!!!!!!!!!
   	    checkConstruction(result);
   	    return result;
   	}
   }*/

   //TODO TypeSV TypeMC

expressionSV : SVIDENTIFIER;
	//return factory.getExpressionSV(token.image);
catchSV: SVIDENTIFIER;
  // CatchSVWrapper factory.getCatchSV(token.image);

ccatchSV: SVIDENTIFIER;
//ccatchSVWrapper factory.getCcatchSV(token.image);

statementSV : SVIDENTIFIER;
//StatementSVWrapper factory.getStatementSV(token.image);

variableSV : SVIDENTIFIER;
executionContextSV : SVIDENTIFIER;

rMethodCallStatement
    : 'method-frame' '('
        (variableSV ',')?
        (executionContext | executionContextSV)
      	')' ':'
      block
    ;

/*{
    RMethodCallStatement result;
    ProgramVariableSVWrapper res = null;
    ExecutionContext exec = null;
    StatementBlock block;
}
{
    "method-frame"  "("
	(LOOKAHEAD(2) res = VariableSV() "," )?
	(LOOKAHEAD(2) exec = ExecutionContext() |
	 exec = ExecutionContextSV()) ")"
	":"
	block = Block()
    {
	result = factory.createRMethodCallStatement(res, exec, block);
	checkConstruction(result);
	return result;
    }
}*/
/*
LocalVariableDeclaration SVLocalVariableDeclaration() :
{
    LocalVariableDeclaration result;
    ASTList<VariableSpecification> vl = new ASTArrayList<VariableSpecification>(1);
    TypeReference tr;
    VariableSpecification var;
}
{
    {
	result = factory.createLocalVariableDeclaration();
	setPrefixInfo(result);
    }
    [ "final"
    {
	Final fi = factory.createFinal();
	setPrefixInfo(fi);
	result.setDeclarationSpecifiers(new ASTArrayList<DeclarationSpecifier>(fi));
    }
    |
      "ghost"
    {
    	Ghost g = new Ghost();
    	setPrefixInfo(g);
    	result.setDeclarationSpecifiers(new ASTArrayList<DeclarationSpecifier>(g));
    }
    ]
	(tr = TypeMC() | tr = TypeSV() | tr = Type() )
	var = SVVariableDeclarator(false) {vl.add(var);}
    {
	result.setTypeReference(tr);
	result.setVariableSpecifications(vl);
	checkConstruction(result);

	return result;
    }
}
*/

/*
StatementBlock StartBlock() :
{
    StatementBlock result = null;
    ASTList<Statement> sl = new ASTArrayList<Statement>();
    Statement stat;
    ExecCtxtSVWrapper ec = null;
    TypeSVWrapper tr = null;
    MethodSignatureSVWrapper pm = null;
    ExpressionSVWrapper sv = null;
}
{
   "{" (   LOOKAHEAD(2)
           ( <DOT> ( LOOKAHEAD(2)
		     pm=MethodSignatureSV() "@" tr = TypeSV()  "(" (sv = ExpressionSV())? ")" |
	             ec = ExecutionContextSV() ))?
            <CONTEXTSTART>
            {
              if (tr == null) {
                 result = factory.createContextStatementBlock(ec);
	      } else {
                 result = factory.createContextStatementBlock(tr, pm, sv);
	      }
              setPrefixInfo(result);
            }
           (stat = BlockStatement() { sl.add(stat); } )*
           <CONTEXTEND>
       |
	  ({
             result = factory.createStatementBlock();
             setPrefixInfo(result);
           }
           ( stat = BlockStatement()
               {
                   sl.add(stat);
               }
           )*)
      )
   "}" {
         result.setBody(sl);
         checkConstruction(result);
         return result;
       }
}
*/

jumpLabelSV: SVIDENTIFIER;
//	    return factory.getJumpLabelSV(token.image);

typeMC
    :  TYPEOF '(' expression ')';
           /*{ result = factory.createRKeYMetaConstructType();
             ((RKeYMetaConstructType)result).setChild(e);
             ((RKeYMetaConstructType)result).setName("#typeof");
             return result;
           } */
/*{
    RKeYMetaConstructType result;
    Expression e;
}
{*/


keYMetaConstructStatement
    : '#unwind-loop' '('
        innerLabel=jumpLabelSV ',' outerLabel=jumpLabelSV ','
        (whileStatement | forStatement | doWhileStatement)
        ')' ';'
    | '#unwind-loop-bounded'
      '('
          innerLabel=jumpLabelSV ',' outerLabel=jumpLabelSV ','
          (whileStatement | forStatement | doWhileStatement)
      ')' ';'
    | FORINITUNFOLDTRANSFORMER '(' forInit ')' ';'
    | LOOPSCOPEINVARIANTTRANSFORMER '(' whileStatement ')' ';'
    | UNPACK '(' forStatement ')' ';'
    | '#for-to-while' '(' innerLabel=jumpLabelSV ',' outerLabel=jumpLabelSV ','
       statement ')'
    | SWITCHTOIF '(' statement ')'
    | '#do-break' '(' labeledStatement ')' ';'
    | '#evaluate-arguments' '(' statementExpression ')' ';'
    | '#replace' '(' statement ',' variableSV ')' ';'
	  |	   '#method-call' '(' primary ')' ';'
	  | '#expand-method-body' '(' statement (',' variableSV )?  ')' ';'
	  | '#constructor-call' '(' sv = SVIDENTIFIER ',' consRef = SVIDENTIFIER ')' ';'
	  | '#special-constructor-call' '(' expr=SVIDENTIFIER ')' ';'
	  |	'#post-work' '(' expr=SVIDENTIFIER ')' ';'
	  | '#static-initialisation' '(' primary ')' ';'
	  | '#resolve-multiple-var-decl' '(' statement ')' ';'
	  | '#array-post-declaration' '(' statement ')' ';'
	  | '#init-array-creation' '(' variableSV ',' expressionSV ')' ';'
	  | '#init-array-creation-transient' '(' variableSV ',' expressionSV ')' ';'
	  | '#init-array-assignments' '(' variableSV ',' expressionSV ')' ';'
    | '#enhancedfor-elim' '(' forStatement ')' ';'
    | REATTACHLOOPINVARIANT '(' whileStatement ')' ';'
    ;


//TODO passive expression

identifier
    : IDENTIFIER | ImplicitIdentifier | DL_EMBEDDED_FUNCTION
    | SEQ | MAP | SET |LOCSET | BIGINT
    | {schemeMode}? SVIDENTIFIER //	result = factory.getExpressionSV(token.image);
    ;

executionContext
    : 'source=' identifier formalParameters AT classContext=typeType
      ( COMMA THIS ASSIGN runtimeInstance=expression )?
    ;

ccatchBlock
    : CCATCH LPAREN
      type=(RETURNTYPE|BREAKTYPE|CONTINUETYPE)
      (identifier | formalParameter | MUL)?
      RPAREN block
    ;

catchClause
    : CATCH '(' variableModifier* catchType identifier ')' block
    ;

catchType
    : qualifiedName ('|' qualifiedName)*
    ;

finallyBlock
    : FINALLY block
    ;

resourceSpecification
    : '(' resources ';'? ')'
    ;

resources
    : resource (';' resource)*
    ;

resource
    : variableModifier* classOrInterfaceType variableDeclaratorId '=' expression
    ;

/** Matches cases then statements, both of which are mandatory.
 *  To handle empty cases at the end, we add switchLabel* to statement.
 */
switchBlockStatementGroup
    : (switchLabel ':')+ blockStatement+
    ;

switchRule:
      switchLabel '->' expression
    | switchLabel '->' block
    | switchLabel '->' throwStatement
    ;

switchLabel
    : CASE (constantExpression=expression | enumConstantName=identifier)
    | DEFAULT
    ;

forControl
    : enhancedForControl
    | forInit? SEMI expression? SEMI forUpdate=expressionList?
    ;

forInit
    : localVariableDeclaration
    | expressionList
    ;

enhancedForControl
    : variableModifier* typeType variableDeclaratorId ':' expression
    ;

// EXPRESSIONS

parExpression
    : '(' expression ')'
    ;

expressionList
    : expression (',' expression)*
    ;

methodCall
    : identifier '(' expressionList? ')'
    | THIS '(' expressionList? ')'
    | SUPER '(' expressionList? ')'
    ;

expression
    : primary               #ignore
    | expression bop='.'
      ( identifier
      | methodCall
      | THIS
      | NEW nonWildcardTypeArguments? innerCreator
      | SUPER superSuffix
      | explicitGenericInvocation
      )
      #accessExpr
    | expression '[' expression ']' #arrayAccess
    | methodCall                    #methodCallExpr
    | NEW creator                   #instantiation
    | '(' typeType ')' expression   #castExpression
    | expression postfix=('++' | '--') #postfixExpression
    | prefix=('+'|'-'|'++'|'--') expression #prefixExpression
    | prefix=('~'|'!') expression           #unaryExpression
    | // Java 12+
      SWITCH parExpression '{' (switchRule+ | switchBlockStatementGroup* switchLabel*) '}'#switchExpression
    | expression bop=('*'|'/'|'%') expression #multiplicativeExpression
    | expression bop=('+'|'-') expression     #additiveExpression
    | expression bop=('<<' | '>>>' | '>>') expression #shiftExpression
    | expression bop=('<=' | '>=' | '>' | '<') expression #relationalExpression
    | expression bop=INSTANCEOF typeType       #instanceOfExpression
    | expression bop=('==' | '!=') expression  #equalityExpression
    | expression bop='&' expression            #andExpression
    | expression bop='^' expression            #exclusvieOrExpression
    | expression bop='|' expression            #inclusiveOrExpression
    | expression bop='&&' expression           #conditionalAndExpression
    | expression bop='||' expression           #conditionalOrExpression
    | <assoc=right> expression bop='?' expression ':' expression #conditionalExpression
    | <assoc=right> expression
      bop=('=' | '+=' | '-=' | '*=' | '/=' | '&=' | '|=' | '^=' | '>>=' | '>>>=' | '<<=' | '%=')
      expression #assignExpression
    | lambdaExpression #ignore2 // Java8

    // Java 8 methodReference
    | expression '::' typeArguments? identifier #methodReference1
    | typeType '::' (typeArguments? identifier | NEW) #methodReference2
    | classType '::' typeArguments? NEW #methodReference3
    ;

/*
| adtGetter
  | generalEscapeExpression()
	;


generalEscapeExpression
  : (DL_EMBEDDED_FUNCTION | MAP_FUNCTION)
    LPAREN (expression (COMMA expression())*)? RPAREN
  ;

adtGetter
  : '\\indexOf' LPAREN expression COMMA expression RPAREN
  | '\\seq_length' LPAREN expression RPAREN
  | '\\seq_get' LPAREN expression COMMA expression RPAREN
  ;*/

// Java8
lambdaExpression
    : lambdaParameters '->' lambdaBody
    ;

// Java8
lambdaParameters
    : identifier
    | '(' formalParameterList? ')'
    | '(' identifier (',' identifier)* ')'
    ;

// Java8
lambdaBody
    : expression
    | block
    ;

primary
    : LPAREN expression RPAREN
    | THIS
    | SUPER
    | literal
    | identifier
    | typeTypeOrVoid '.' CLASS
    | nonWildcardTypeArguments (explicitGenericInvocationSuffix | THIS arguments)
    ;

classType
    : (classOrInterfaceType '.')? annotation* identifier typeArguments?
    ;

creator
    : nonWildcardTypeArguments createdName classCreatorRest
    | createdName (arrayCreatorRest | classCreatorRest)
    ;

createdName
    : identifier typeArgumentsOrDiamond? ('.' identifier typeArgumentsOrDiamond?)*
    | primitiveType
    ;

innerCreator
    : identifier nonWildcardTypeArgumentsOrDiamond? classCreatorRest
    ;

arrayCreatorRest
    : '[' (']' ('[' ']')* arrayInitializer | expression ']' ('[' expression ']')* ('[' ']')*)
    ;

classCreatorRest
    : arguments classBody?
    ;

explicitGenericInvocation
    : nonWildcardTypeArguments explicitGenericInvocationSuffix
    ;

typeArgumentsOrDiamond
    : '<' '>'
    | typeArguments
    ;

nonWildcardTypeArgumentsOrDiamond
    : '<' '>'
    | nonWildcardTypeArguments
    ;

nonWildcardTypeArguments
    : '<' typeList '>'
    ;

typeList
    : typeType (',' typeType)*
    ;

typeType
    : annotation? (classOrInterfaceType | primitiveType) (LBRACK RBRACK)*
    ;

primitiveType
    : BOOLEAN
    | CHAR
    | BYTE
    | SHORT
    | INT
    | LONG
    | FLOAT
    | DOUBLE
    | BIGINT
    | REAL
    | LOCSET
    | SEQ
    | FREE
    | MAP
    ;

typeArguments
    : LT typeArgument (COMMA typeArgument)* GT
    ;

superSuffix
    : arguments
    | '.' identifier arguments?
    ;

explicitGenericInvocationSuffix
    : SUPER superSuffix
    | identifier arguments
    ;

arguments
    : '(' expressionList? ')'
    ;

keymeta//TODO find place
    : '#create-object' '(' expressionSV ')'
    | '#length-reference' '(' expressionSV ')'
    ;

/***** LEXER *****/

// Keywords

ABSTRACT:           'abstract';
ASSERT:             'assert';
BOOLEAN:            'boolean';
BREAK:              'break';
BYTE:               'byte';
CASE:               'case';
CATCH:              'catch';
CHAR:               'char';
CLASS:              'class';
CONST:              'const';
CONTINUE:           'continue';
DEFAULT:            'default';
DO:                 'do';
DOUBLE:             'double';
ELSE:               'else';
ENUM:               'enum';
EXTENDS:            'extends';
FINAL:              'final';
FINALLY:            'finally';
FLOAT:              'float';
FOR:                'for';
IF:                 'if';
GOTO:               'goto';
IMPLEMENTS:         'implements';
IMPORT:             'import';
INSTANCEOF:         'instanceof';
INT:                'int';
INTERFACE:          'interface';
LONG:               'long';
NATIVE:             'native';
NEW:                'new';
PACKAGE:            'package';
PRIVATE:            'private';
PROTECTED:          'protected';
PUBLIC:             'public';
RETURN:             'return';
SHORT:              'short';
STATIC:             'static';
STRICTFP:           'strictfp';
SUPER:              'super';
SWITCH:             'switch';
SYNCHRONIZED:       'synchronized';
THIS:               'this';
THROW:              'throw';
THROWS:             'throws';
TRANSIENT:          'transient';
TRY:                'try';
VOID:               'void';
VOLATILE:           'volatile';
WHILE:              'while';
YIELD:              'yield';

/// KEY STUFF

BIGINT: '\\bigint';
REAL: '\\real';
BREAKTYPE: '\\Break';
CCATCH: 'ccatch';
CONTINUETYPE: '\\Continue';
EXEC: 'exec';
FREE: '\\free';
LOCSET: '\\locset';
LOOPSCOPE: 'loop-scope';
MAP: '\\map';
MERGE_POINT: 'merge_point';
METHODFRAME: 'method-frame';
RETURNTYPE: '\\Return';
SEQ : '\\seq';
SET : '\\set';
TRANSACTIONBEGIN : '#beginJavaCardTransaction';
TRANSACTIONCOMMIT : '#commitJavaCardTransaction';
TRANSACTIONFINISH : '#finishJavaCardTransaction';
TRANSACTIONABORT : '#abortJavaCardTransaction';
GHOST: 'ghost';
ISSTATIC: '#isstatic';
EVALARGS: '#evaluate-arguments';
REPLACEARGS: '#replace';
CONTEXTSTART: '..';
//CONTEXTEND: '...'; superseded by ELLIPSIS
TYPEOF: '#typeof';
SWITCHTOIF: '#switch-to-if';
UNPACK: '#unpack';
REATTACHLOOPINVARIANT: '#reattachLoopInvariant';
FORINITUNFOLDTRANSFORMER: '#forInitUnfoldTransformer';
LOOPSCOPEINVARIANTTRANSFORMER: '#loopScopeInvariantTransformer';
SETSV: '#set';

EMPTYSETLITERAL : '\\empty';
EMPTYSEQLITERAL : '\\seq_empty';
EMPTYMAPLITERAL : '\\map_empty';

DL_EMBEDDED_FUNCTION:  '\\dl_' Letter (LetterOrDigit)*;
MAP_FUNCTION:
      '\\map_get'
    | '\\map_singleton'
    | '\\map_override'
    | '\\seq_2_map'
    | '\\map_remove'
    | '\\map_update'
    | '\\in_domain'
    | '\\domain_implies_created'
    | '\\map_size'
    | '\\is_finite'
;

ImplicitIdentifier: '`' Letter (LetterOrDigit)* '`';



// Literals

DECIMAL_LITERAL:    ('0' | [1-9] (Digits? | '_'+ Digits)) [lL]?;
HEX_LITERAL:        '0' [xX] [0-9a-fA-F] ([0-9a-fA-F_]* [0-9a-fA-F])? [lL]?;
OCT_LITERAL:        '0' '_'* [0-7] ([0-7_]* [0-7])? [lL]?;
BINARY_LITERAL:     '0' [bB] [01] ([01_]* [01])? [lL]?;

FLOAT_LITERAL:      (Digits '.' Digits? | '.' Digits) ExponentPart? [fFdD]?
             |       Digits (ExponentPart [fFdD]? | [fFdD])
             ;

HEX_FLOAT_LITERAL:  '0' [xX] (HexDigits '.'? | HexDigits? '.' HexDigits) [pP] [+-]? Digits [fFdD]?;

BOOL_LITERAL:       'true'
            |       'false'
            ;

CHAR_LITERAL:       '\'' (~['\\\r\n] | EscapeSequence) '\'';

STRING_LITERAL:     '"' (~["\\\r\n] | EscapeSequence)* '"';

NULL_LITERAL:       'null';

TEXT_BLOCK:         '"""' .*? '"""';


// Separators

LPAREN:             '(';
RPAREN:             ')';
LBRACE:             '{';
RBRACE:             '}';
LBRACK:             '[';
RBRACK:             ']';
SEMI:               ';';
COMMA:              ',';
DOT:                '.';

// Operators

ASSIGN:             '=';
GT:                 '>';
LT:                 '<';
BANG:               '!';
TILDE:              '~';
QUESTION:           '?';
COLON:              ':';
EQUAL:              '==';
LE:                 '<=';
GE:                 '>=';
NOTEQUAL:           '!=';
AND:                '&&';
OR:                 '||';
INC:                '++';
DEC:                '--';
ADD:                '+';
SUB:                '-';
MUL:                '*';
DIV:                '/';
BITAND:             '&';
BITOR:              '|';
CARET:              '^';
MOD:                '%';

ADD_ASSIGN:         '+=';
SUB_ASSIGN:         '-=';
MUL_ASSIGN:         '*=';
DIV_ASSIGN:         '/=';
AND_ASSIGN:         '&=';
OR_ASSIGN:          '|=';
XOR_ASSIGN:         '^=';
MOD_ASSIGN:         '%=';
LSHIFT_ASSIGN:      '<<=';
RSHIFT_ASSIGN:      '>>=';
URSHIFT_ASSIGN:     '>>>=';

// Java 8 tokens

ARROW:              '->';
COLONCOLON:         '::';

// Additional symbols not defined in the lexical specification

AT:                 '@';
ELLIPSIS:           '...';

// Whitespace and comments

WS:                 [ \t\r\n\u000C]+ -> channel(HIDDEN);
COMMENT:            '/*' .*? '*/'    -> channel(HIDDEN);
LINE_COMMENT:       '//' ~[\r\n]*    -> channel(HIDDEN);

// identifiers

IDENTIFIER:         Letter LetterOrDigit*;
SVIDENTIFIER:       '#' IDENTIFIER;

// Fragment rules

fragment ExponentPart
    : [eE] [+-]? Digits
    ;

fragment EscapeSequence
    : '\\' [btnfr"'\\]
    | '\\' ([0-3]? [0-7])? [0-7]
    | '\\' 'u'+ HexDigit HexDigit HexDigit HexDigit
    ;

fragment HexDigits
    : HexDigit ((HexDigit | '_')* HexDigit)?
    ;

fragment HexDigit
    : [0-9a-fA-F]
    ;

fragment Digits
    : [0-9] ([0-9_]* [0-9])?
    ;

fragment LetterOrDigit
    : Letter
    | [0-9]
    ;

fragment Letter
    : [a-zA-Z$_] // these are the "java letters" below 0x7F
    | ~[\u0000-\u007F\uD800-\uDBFF] // covers all characters above 0x7F which are not a surrogate
    | [\uD800-\uDBFF] [\uDC00-\uDFFF] // covers UTF-16 surrogate pairs encodings for U+10000 to U+10FFFF
    ;