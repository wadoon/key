// Generated from Solidity.g4 by ANTLR 4.9.3
package de.uka.ilkd.key.parser.solidity;

import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link SolidityParser}.
 */
public interface SolidityListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link SolidityParser#sourceUnit}.
	 * @param ctx the parse tree
	 */
	void enterSourceUnit(SolidityParser.SourceUnitContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#sourceUnit}.
	 * @param ctx the parse tree
	 */
	void exitSourceUnit(SolidityParser.SourceUnitContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#pragmaDirective}.
	 * @param ctx the parse tree
	 */
	void enterPragmaDirective(SolidityParser.PragmaDirectiveContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#pragmaDirective}.
	 * @param ctx the parse tree
	 */
	void exitPragmaDirective(SolidityParser.PragmaDirectiveContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#pragmaName}.
	 * @param ctx the parse tree
	 */
	void enterPragmaName(SolidityParser.PragmaNameContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#pragmaName}.
	 * @param ctx the parse tree
	 */
	void exitPragmaName(SolidityParser.PragmaNameContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#pragmaValue}.
	 * @param ctx the parse tree
	 */
	void enterPragmaValue(SolidityParser.PragmaValueContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#pragmaValue}.
	 * @param ctx the parse tree
	 */
	void exitPragmaValue(SolidityParser.PragmaValueContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#version}.
	 * @param ctx the parse tree
	 */
	void enterVersion(SolidityParser.VersionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#version}.
	 * @param ctx the parse tree
	 */
	void exitVersion(SolidityParser.VersionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#versionOperator}.
	 * @param ctx the parse tree
	 */
	void enterVersionOperator(SolidityParser.VersionOperatorContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#versionOperator}.
	 * @param ctx the parse tree
	 */
	void exitVersionOperator(SolidityParser.VersionOperatorContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#versionConstraint}.
	 * @param ctx the parse tree
	 */
	void enterVersionConstraint(SolidityParser.VersionConstraintContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#versionConstraint}.
	 * @param ctx the parse tree
	 */
	void exitVersionConstraint(SolidityParser.VersionConstraintContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#importDeclaration}.
	 * @param ctx the parse tree
	 */
	void enterImportDeclaration(SolidityParser.ImportDeclarationContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#importDeclaration}.
	 * @param ctx the parse tree
	 */
	void exitImportDeclaration(SolidityParser.ImportDeclarationContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#importDirective}.
	 * @param ctx the parse tree
	 */
	void enterImportDirective(SolidityParser.ImportDirectiveContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#importDirective}.
	 * @param ctx the parse tree
	 */
	void exitImportDirective(SolidityParser.ImportDirectiveContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#contractDefinition}.
	 * @param ctx the parse tree
	 */
	void enterContractDefinition(SolidityParser.ContractDefinitionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#contractDefinition}.
	 * @param ctx the parse tree
	 */
	void exitContractDefinition(SolidityParser.ContractDefinitionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#inheritanceSpecifier}.
	 * @param ctx the parse tree
	 */
	void enterInheritanceSpecifier(SolidityParser.InheritanceSpecifierContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#inheritanceSpecifier}.
	 * @param ctx the parse tree
	 */
	void exitInheritanceSpecifier(SolidityParser.InheritanceSpecifierContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#contractPart}.
	 * @param ctx the parse tree
	 */
	void enterContractPart(SolidityParser.ContractPartContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#contractPart}.
	 * @param ctx the parse tree
	 */
	void exitContractPart(SolidityParser.ContractPartContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#stateVariableDeclaration}.
	 * @param ctx the parse tree
	 */
	void enterStateVariableDeclaration(SolidityParser.StateVariableDeclarationContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#stateVariableDeclaration}.
	 * @param ctx the parse tree
	 */
	void exitStateVariableDeclaration(SolidityParser.StateVariableDeclarationContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#usingForDeclaration}.
	 * @param ctx the parse tree
	 */
	void enterUsingForDeclaration(SolidityParser.UsingForDeclarationContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#usingForDeclaration}.
	 * @param ctx the parse tree
	 */
	void exitUsingForDeclaration(SolidityParser.UsingForDeclarationContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#structDefinition}.
	 * @param ctx the parse tree
	 */
	void enterStructDefinition(SolidityParser.StructDefinitionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#structDefinition}.
	 * @param ctx the parse tree
	 */
	void exitStructDefinition(SolidityParser.StructDefinitionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#constructorDefinition}.
	 * @param ctx the parse tree
	 */
	void enterConstructorDefinition(SolidityParser.ConstructorDefinitionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#constructorDefinition}.
	 * @param ctx the parse tree
	 */
	void exitConstructorDefinition(SolidityParser.ConstructorDefinitionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#modifierDefinition}.
	 * @param ctx the parse tree
	 */
	void enterModifierDefinition(SolidityParser.ModifierDefinitionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#modifierDefinition}.
	 * @param ctx the parse tree
	 */
	void exitModifierDefinition(SolidityParser.ModifierDefinitionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#modifierInvocation}.
	 * @param ctx the parse tree
	 */
	void enterModifierInvocation(SolidityParser.ModifierInvocationContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#modifierInvocation}.
	 * @param ctx the parse tree
	 */
	void exitModifierInvocation(SolidityParser.ModifierInvocationContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#functionDefinition}.
	 * @param ctx the parse tree
	 */
	void enterFunctionDefinition(SolidityParser.FunctionDefinitionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#functionDefinition}.
	 * @param ctx the parse tree
	 */
	void exitFunctionDefinition(SolidityParser.FunctionDefinitionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#returnParameters}.
	 * @param ctx the parse tree
	 */
	void enterReturnParameters(SolidityParser.ReturnParametersContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#returnParameters}.
	 * @param ctx the parse tree
	 */
	void exitReturnParameters(SolidityParser.ReturnParametersContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#modifierList}.
	 * @param ctx the parse tree
	 */
	void enterModifierList(SolidityParser.ModifierListContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#modifierList}.
	 * @param ctx the parse tree
	 */
	void exitModifierList(SolidityParser.ModifierListContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#eventDefinition}.
	 * @param ctx the parse tree
	 */
	void enterEventDefinition(SolidityParser.EventDefinitionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#eventDefinition}.
	 * @param ctx the parse tree
	 */
	void exitEventDefinition(SolidityParser.EventDefinitionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#enumValue}.
	 * @param ctx the parse tree
	 */
	void enterEnumValue(SolidityParser.EnumValueContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#enumValue}.
	 * @param ctx the parse tree
	 */
	void exitEnumValue(SolidityParser.EnumValueContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#enumDefinition}.
	 * @param ctx the parse tree
	 */
	void enterEnumDefinition(SolidityParser.EnumDefinitionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#enumDefinition}.
	 * @param ctx the parse tree
	 */
	void exitEnumDefinition(SolidityParser.EnumDefinitionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#specDefinition}.
	 * @param ctx the parse tree
	 */
	void enterSpecDefinition(SolidityParser.SpecDefinitionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#specDefinition}.
	 * @param ctx the parse tree
	 */
	void exitSpecDefinition(SolidityParser.SpecDefinitionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code specOnlyIf}
	 * labeled alternative in {@link SolidityParser#specExpression}.
	 * @param ctx the parse tree
	 */
	void enterSpecOnlyIf(SolidityParser.SpecOnlyIfContext ctx);
	/**
	 * Exit a parse tree produced by the {@code specOnlyIf}
	 * labeled alternative in {@link SolidityParser#specExpression}.
	 * @param ctx the parse tree
	 */
	void exitSpecOnlyIf(SolidityParser.SpecOnlyIfContext ctx);
	/**
	 * Enter a parse tree produced by the {@code specAssumes}
	 * labeled alternative in {@link SolidityParser#specExpression}.
	 * @param ctx the parse tree
	 */
	void enterSpecAssumes(SolidityParser.SpecAssumesContext ctx);
	/**
	 * Exit a parse tree produced by the {@code specAssumes}
	 * labeled alternative in {@link SolidityParser#specExpression}.
	 * @param ctx the parse tree
	 */
	void exitSpecAssumes(SolidityParser.SpecAssumesContext ctx);
	/**
	 * Enter a parse tree produced by the {@code specOnSuccess}
	 * labeled alternative in {@link SolidityParser#specExpression}.
	 * @param ctx the parse tree
	 */
	void enterSpecOnSuccess(SolidityParser.SpecOnSuccessContext ctx);
	/**
	 * Exit a parse tree produced by the {@code specOnSuccess}
	 * labeled alternative in {@link SolidityParser#specExpression}.
	 * @param ctx the parse tree
	 */
	void exitSpecOnSuccess(SolidityParser.SpecOnSuccessContext ctx);
	/**
	 * Enter a parse tree produced by the {@code specContractInvariant}
	 * labeled alternative in {@link SolidityParser#specExpression}.
	 * @param ctx the parse tree
	 */
	void enterSpecContractInvariant(SolidityParser.SpecContractInvariantContext ctx);
	/**
	 * Exit a parse tree produced by the {@code specContractInvariant}
	 * labeled alternative in {@link SolidityParser#specExpression}.
	 * @param ctx the parse tree
	 */
	void exitSpecContractInvariant(SolidityParser.SpecContractInvariantContext ctx);
	/**
	 * Enter a parse tree produced by the {@code specLibraryInvariant}
	 * labeled alternative in {@link SolidityParser#specExpression}.
	 * @param ctx the parse tree
	 */
	void enterSpecLibraryInvariant(SolidityParser.SpecLibraryInvariantContext ctx);
	/**
	 * Exit a parse tree produced by the {@code specLibraryInvariant}
	 * labeled alternative in {@link SolidityParser#specExpression}.
	 * @param ctx the parse tree
	 */
	void exitSpecLibraryInvariant(SolidityParser.SpecLibraryInvariantContext ctx);
	/**
	 * Enter a parse tree produced by the {@code specAssignable}
	 * labeled alternative in {@link SolidityParser#specExpression}.
	 * @param ctx the parse tree
	 */
	void enterSpecAssignable(SolidityParser.SpecAssignableContext ctx);
	/**
	 * Exit a parse tree produced by the {@code specAssignable}
	 * labeled alternative in {@link SolidityParser#specExpression}.
	 * @param ctx the parse tree
	 */
	void exitSpecAssignable(SolidityParser.SpecAssignableContext ctx);
	/**
	 * Enter a parse tree produced by the {@code specObservesInvariantFor}
	 * labeled alternative in {@link SolidityParser#specExpression}.
	 * @param ctx the parse tree
	 */
	void enterSpecObservesInvariantFor(SolidityParser.SpecObservesInvariantForContext ctx);
	/**
	 * Exit a parse tree produced by the {@code specObservesInvariantFor}
	 * labeled alternative in {@link SolidityParser#specExpression}.
	 * @param ctx the parse tree
	 */
	void exitSpecObservesInvariantFor(SolidityParser.SpecObservesInvariantForContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#parameterList}.
	 * @param ctx the parse tree
	 */
	void enterParameterList(SolidityParser.ParameterListContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#parameterList}.
	 * @param ctx the parse tree
	 */
	void exitParameterList(SolidityParser.ParameterListContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#parameter}.
	 * @param ctx the parse tree
	 */
	void enterParameter(SolidityParser.ParameterContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#parameter}.
	 * @param ctx the parse tree
	 */
	void exitParameter(SolidityParser.ParameterContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#eventParameterList}.
	 * @param ctx the parse tree
	 */
	void enterEventParameterList(SolidityParser.EventParameterListContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#eventParameterList}.
	 * @param ctx the parse tree
	 */
	void exitEventParameterList(SolidityParser.EventParameterListContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#eventParameter}.
	 * @param ctx the parse tree
	 */
	void enterEventParameter(SolidityParser.EventParameterContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#eventParameter}.
	 * @param ctx the parse tree
	 */
	void exitEventParameter(SolidityParser.EventParameterContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#functionTypeParameterList}.
	 * @param ctx the parse tree
	 */
	void enterFunctionTypeParameterList(SolidityParser.FunctionTypeParameterListContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#functionTypeParameterList}.
	 * @param ctx the parse tree
	 */
	void exitFunctionTypeParameterList(SolidityParser.FunctionTypeParameterListContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#functionTypeParameter}.
	 * @param ctx the parse tree
	 */
	void enterFunctionTypeParameter(SolidityParser.FunctionTypeParameterContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#functionTypeParameter}.
	 * @param ctx the parse tree
	 */
	void exitFunctionTypeParameter(SolidityParser.FunctionTypeParameterContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#variableDeclaration}.
	 * @param ctx the parse tree
	 */
	void enterVariableDeclaration(SolidityParser.VariableDeclarationContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#variableDeclaration}.
	 * @param ctx the parse tree
	 */
	void exitVariableDeclaration(SolidityParser.VariableDeclarationContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#typeName}.
	 * @param ctx the parse tree
	 */
	void enterTypeName(SolidityParser.TypeNameContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#typeName}.
	 * @param ctx the parse tree
	 */
	void exitTypeName(SolidityParser.TypeNameContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#userDefinedTypeName}.
	 * @param ctx the parse tree
	 */
	void enterUserDefinedTypeName(SolidityParser.UserDefinedTypeNameContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#userDefinedTypeName}.
	 * @param ctx the parse tree
	 */
	void exitUserDefinedTypeName(SolidityParser.UserDefinedTypeNameContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#mapping}.
	 * @param ctx the parse tree
	 */
	void enterMapping(SolidityParser.MappingContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#mapping}.
	 * @param ctx the parse tree
	 */
	void exitMapping(SolidityParser.MappingContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#functionTypeName}.
	 * @param ctx the parse tree
	 */
	void enterFunctionTypeName(SolidityParser.FunctionTypeNameContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#functionTypeName}.
	 * @param ctx the parse tree
	 */
	void exitFunctionTypeName(SolidityParser.FunctionTypeNameContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#storageLocation}.
	 * @param ctx the parse tree
	 */
	void enterStorageLocation(SolidityParser.StorageLocationContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#storageLocation}.
	 * @param ctx the parse tree
	 */
	void exitStorageLocation(SolidityParser.StorageLocationContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#stateMutability}.
	 * @param ctx the parse tree
	 */
	void enterStateMutability(SolidityParser.StateMutabilityContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#stateMutability}.
	 * @param ctx the parse tree
	 */
	void exitStateMutability(SolidityParser.StateMutabilityContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#block}.
	 * @param ctx the parse tree
	 */
	void enterBlock(SolidityParser.BlockContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#block}.
	 * @param ctx the parse tree
	 */
	void exitBlock(SolidityParser.BlockContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#uncheckedBlock}.
	 * @param ctx the parse tree
	 */
	void enterUncheckedBlock(SolidityParser.UncheckedBlockContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#uncheckedBlock}.
	 * @param ctx the parse tree
	 */
	void exitUncheckedBlock(SolidityParser.UncheckedBlockContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#statement}.
	 * @param ctx the parse tree
	 */
	void enterStatement(SolidityParser.StatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#statement}.
	 * @param ctx the parse tree
	 */
	void exitStatement(SolidityParser.StatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#placeHolderStatement}.
	 * @param ctx the parse tree
	 */
	void enterPlaceHolderStatement(SolidityParser.PlaceHolderStatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#placeHolderStatement}.
	 * @param ctx the parse tree
	 */
	void exitPlaceHolderStatement(SolidityParser.PlaceHolderStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#expressionStatement}.
	 * @param ctx the parse tree
	 */
	void enterExpressionStatement(SolidityParser.ExpressionStatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#expressionStatement}.
	 * @param ctx the parse tree
	 */
	void exitExpressionStatement(SolidityParser.ExpressionStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#ifStatement}.
	 * @param ctx the parse tree
	 */
	void enterIfStatement(SolidityParser.IfStatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#ifStatement}.
	 * @param ctx the parse tree
	 */
	void exitIfStatement(SolidityParser.IfStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#whileStatement}.
	 * @param ctx the parse tree
	 */
	void enterWhileStatement(SolidityParser.WhileStatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#whileStatement}.
	 * @param ctx the parse tree
	 */
	void exitWhileStatement(SolidityParser.WhileStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#simpleStatement}.
	 * @param ctx the parse tree
	 */
	void enterSimpleStatement(SolidityParser.SimpleStatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#simpleStatement}.
	 * @param ctx the parse tree
	 */
	void exitSimpleStatement(SolidityParser.SimpleStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#forStatement}.
	 * @param ctx the parse tree
	 */
	void enterForStatement(SolidityParser.ForStatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#forStatement}.
	 * @param ctx the parse tree
	 */
	void exitForStatement(SolidityParser.ForStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#inlineAssemblyStatement}.
	 * @param ctx the parse tree
	 */
	void enterInlineAssemblyStatement(SolidityParser.InlineAssemblyStatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#inlineAssemblyStatement}.
	 * @param ctx the parse tree
	 */
	void exitInlineAssemblyStatement(SolidityParser.InlineAssemblyStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#doWhileStatement}.
	 * @param ctx the parse tree
	 */
	void enterDoWhileStatement(SolidityParser.DoWhileStatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#doWhileStatement}.
	 * @param ctx the parse tree
	 */
	void exitDoWhileStatement(SolidityParser.DoWhileStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#continueStatement}.
	 * @param ctx the parse tree
	 */
	void enterContinueStatement(SolidityParser.ContinueStatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#continueStatement}.
	 * @param ctx the parse tree
	 */
	void exitContinueStatement(SolidityParser.ContinueStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#breakStatement}.
	 * @param ctx the parse tree
	 */
	void enterBreakStatement(SolidityParser.BreakStatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#breakStatement}.
	 * @param ctx the parse tree
	 */
	void exitBreakStatement(SolidityParser.BreakStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#returnStatement}.
	 * @param ctx the parse tree
	 */
	void enterReturnStatement(SolidityParser.ReturnStatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#returnStatement}.
	 * @param ctx the parse tree
	 */
	void exitReturnStatement(SolidityParser.ReturnStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#throwStatement}.
	 * @param ctx the parse tree
	 */
	void enterThrowStatement(SolidityParser.ThrowStatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#throwStatement}.
	 * @param ctx the parse tree
	 */
	void exitThrowStatement(SolidityParser.ThrowStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#emitStatement}.
	 * @param ctx the parse tree
	 */
	void enterEmitStatement(SolidityParser.EmitStatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#emitStatement}.
	 * @param ctx the parse tree
	 */
	void exitEmitStatement(SolidityParser.EmitStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#variableDeclarationStatement}.
	 * @param ctx the parse tree
	 */
	void enterVariableDeclarationStatement(SolidityParser.VariableDeclarationStatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#variableDeclarationStatement}.
	 * @param ctx the parse tree
	 */
	void exitVariableDeclarationStatement(SolidityParser.VariableDeclarationStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#variableDeclarationList}.
	 * @param ctx the parse tree
	 */
	void enterVariableDeclarationList(SolidityParser.VariableDeclarationListContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#variableDeclarationList}.
	 * @param ctx the parse tree
	 */
	void exitVariableDeclarationList(SolidityParser.VariableDeclarationListContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#identifierList}.
	 * @param ctx the parse tree
	 */
	void enterIdentifierList(SolidityParser.IdentifierListContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#identifierList}.
	 * @param ctx the parse tree
	 */
	void exitIdentifierList(SolidityParser.IdentifierListContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#elementaryTypeName}.
	 * @param ctx the parse tree
	 */
	void enterElementaryTypeName(SolidityParser.ElementaryTypeNameContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#elementaryTypeName}.
	 * @param ctx the parse tree
	 */
	void exitElementaryTypeName(SolidityParser.ElementaryTypeNameContext ctx);
	/**
	 * Enter a parse tree produced by the {@code equivalenceExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterEquivalenceExpression(SolidityParser.EquivalenceExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code equivalenceExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitEquivalenceExpression(SolidityParser.EquivalenceExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code netExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterNetExpression(SolidityParser.NetExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code netExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitNetExpression(SolidityParser.NetExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code additiveExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterAdditiveExpression(SolidityParser.AdditiveExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code additiveExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitAdditiveExpression(SolidityParser.AdditiveExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code tildeExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterTildeExpression(SolidityParser.TildeExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code tildeExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitTildeExpression(SolidityParser.TildeExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code notExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterNotExpression(SolidityParser.NotExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code notExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitNotExpression(SolidityParser.NotExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code parenExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterParenExpression(SolidityParser.ParenExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code parenExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitParenExpression(SolidityParser.ParenExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code preIncOrDecExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterPreIncOrDecExpression(SolidityParser.PreIncOrDecExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code preIncOrDecExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitPreIncOrDecExpression(SolidityParser.PreIncOrDecExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code logicalShiftExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterLogicalShiftExpression(SolidityParser.LogicalShiftExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code logicalShiftExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitLogicalShiftExpression(SolidityParser.LogicalShiftExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code postIncOrDecExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterPostIncOrDecExpression(SolidityParser.PostIncOrDecExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code postIncOrDecExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitPostIncOrDecExpression(SolidityParser.PostIncOrDecExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code andExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterAndExpression(SolidityParser.AndExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code andExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitAndExpression(SolidityParser.AndExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code compExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterCompExpression(SolidityParser.CompExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code compExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitCompExpression(SolidityParser.CompExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code forallExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterForallExpression(SolidityParser.ForallExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code forallExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitForallExpression(SolidityParser.ForallExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code existsExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExistsExpression(SolidityParser.ExistsExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code existsExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExistsExpression(SolidityParser.ExistsExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code bitwiseAndExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterBitwiseAndExpression(SolidityParser.BitwiseAndExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code bitwiseAndExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitBitwiseAndExpression(SolidityParser.BitwiseAndExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code functionCallExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterFunctionCallExpression(SolidityParser.FunctionCallExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code functionCallExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitFunctionCallExpression(SolidityParser.FunctionCallExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code minMaxTypeExprExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterMinMaxTypeExprExpression(SolidityParser.MinMaxTypeExprExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code minMaxTypeExprExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitMinMaxTypeExprExpression(SolidityParser.MinMaxTypeExprExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code primaryExprExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterPrimaryExprExpression(SolidityParser.PrimaryExprExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code primaryExprExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitPrimaryExprExpression(SolidityParser.PrimaryExprExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code bitwiseXorExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterBitwiseXorExpression(SolidityParser.BitwiseXorExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code bitwiseXorExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitBitwiseXorExpression(SolidityParser.BitwiseXorExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code dotExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterDotExpression(SolidityParser.DotExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code dotExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitDotExpression(SolidityParser.DotExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code unaryAdditiveExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterUnaryAdditiveExpression(SolidityParser.UnaryAdditiveExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code unaryAdditiveExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitUnaryAdditiveExpression(SolidityParser.UnaryAdditiveExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code newTypeNameExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterNewTypeNameExpression(SolidityParser.NewTypeNameExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code newTypeNameExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitNewTypeNameExpression(SolidityParser.NewTypeNameExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code assignmentExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterAssignmentExpression(SolidityParser.AssignmentExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code assignmentExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitAssignmentExpression(SolidityParser.AssignmentExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code multiplicativeExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterMultiplicativeExpression(SolidityParser.MultiplicativeExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code multiplicativeExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitMultiplicativeExpression(SolidityParser.MultiplicativeExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code orExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterOrExpression(SolidityParser.OrExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code orExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitOrExpression(SolidityParser.OrExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code powerExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterPowerExpression(SolidityParser.PowerExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code powerExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitPowerExpression(SolidityParser.PowerExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code grossFromExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterGrossFromExpression(SolidityParser.GrossFromExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code grossFromExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitGrossFromExpression(SolidityParser.GrossFromExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code bitwiseOrExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterBitwiseOrExpression(SolidityParser.BitwiseOrExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code bitwiseOrExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitBitwiseOrExpression(SolidityParser.BitwiseOrExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code arrayAccessExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterArrayAccessExpression(SolidityParser.ArrayAccessExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code arrayAccessExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitArrayAccessExpression(SolidityParser.ArrayAccessExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code deleteExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterDeleteExpression(SolidityParser.DeleteExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code deleteExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitDeleteExpression(SolidityParser.DeleteExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code equalityExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterEqualityExpression(SolidityParser.EqualityExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code equalityExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitEqualityExpression(SolidityParser.EqualityExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code grossToExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterGrossToExpression(SolidityParser.GrossToExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code grossToExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitGrossToExpression(SolidityParser.GrossToExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code implicationExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterImplicationExpression(SolidityParser.ImplicationExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code implicationExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitImplicationExpression(SolidityParser.ImplicationExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code oldExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterOldExpression(SolidityParser.OldExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code oldExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitOldExpression(SolidityParser.OldExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code onlyIfExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterOnlyIfExpression(SolidityParser.OnlyIfExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code onlyIfExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitOnlyIfExpression(SolidityParser.OnlyIfExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code resultExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterResultExpression(SolidityParser.ResultExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code resultExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitResultExpression(SolidityParser.ResultExpressionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code ternaryExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterTernaryExpression(SolidityParser.TernaryExpressionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code ternaryExpression}
	 * labeled alternative in {@link SolidityParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitTernaryExpression(SolidityParser.TernaryExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#primaryExpression}.
	 * @param ctx the parse tree
	 */
	void enterPrimaryExpression(SolidityParser.PrimaryExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#primaryExpression}.
	 * @param ctx the parse tree
	 */
	void exitPrimaryExpression(SolidityParser.PrimaryExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#minMaxTypeExpression}.
	 * @param ctx the parse tree
	 */
	void enterMinMaxTypeExpression(SolidityParser.MinMaxTypeExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#minMaxTypeExpression}.
	 * @param ctx the parse tree
	 */
	void exitMinMaxTypeExpression(SolidityParser.MinMaxTypeExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#expressionList}.
	 * @param ctx the parse tree
	 */
	void enterExpressionList(SolidityParser.ExpressionListContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#expressionList}.
	 * @param ctx the parse tree
	 */
	void exitExpressionList(SolidityParser.ExpressionListContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#nameValueList}.
	 * @param ctx the parse tree
	 */
	void enterNameValueList(SolidityParser.NameValueListContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#nameValueList}.
	 * @param ctx the parse tree
	 */
	void exitNameValueList(SolidityParser.NameValueListContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#nameValue}.
	 * @param ctx the parse tree
	 */
	void enterNameValue(SolidityParser.NameValueContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#nameValue}.
	 * @param ctx the parse tree
	 */
	void exitNameValue(SolidityParser.NameValueContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#functionCallArguments}.
	 * @param ctx the parse tree
	 */
	void enterFunctionCallArguments(SolidityParser.FunctionCallArgumentsContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#functionCallArguments}.
	 * @param ctx the parse tree
	 */
	void exitFunctionCallArguments(SolidityParser.FunctionCallArgumentsContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#functionCall}.
	 * @param ctx the parse tree
	 */
	void enterFunctionCall(SolidityParser.FunctionCallContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#functionCall}.
	 * @param ctx the parse tree
	 */
	void exitFunctionCall(SolidityParser.FunctionCallContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#assemblyBlock}.
	 * @param ctx the parse tree
	 */
	void enterAssemblyBlock(SolidityParser.AssemblyBlockContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#assemblyBlock}.
	 * @param ctx the parse tree
	 */
	void exitAssemblyBlock(SolidityParser.AssemblyBlockContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#assemblyItem}.
	 * @param ctx the parse tree
	 */
	void enterAssemblyItem(SolidityParser.AssemblyItemContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#assemblyItem}.
	 * @param ctx the parse tree
	 */
	void exitAssemblyItem(SolidityParser.AssemblyItemContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#assemblyExpression}.
	 * @param ctx the parse tree
	 */
	void enterAssemblyExpression(SolidityParser.AssemblyExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#assemblyExpression}.
	 * @param ctx the parse tree
	 */
	void exitAssemblyExpression(SolidityParser.AssemblyExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#assemblyCall}.
	 * @param ctx the parse tree
	 */
	void enterAssemblyCall(SolidityParser.AssemblyCallContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#assemblyCall}.
	 * @param ctx the parse tree
	 */
	void exitAssemblyCall(SolidityParser.AssemblyCallContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#assemblyLocalDefinition}.
	 * @param ctx the parse tree
	 */
	void enterAssemblyLocalDefinition(SolidityParser.AssemblyLocalDefinitionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#assemblyLocalDefinition}.
	 * @param ctx the parse tree
	 */
	void exitAssemblyLocalDefinition(SolidityParser.AssemblyLocalDefinitionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#assemblyAssignment}.
	 * @param ctx the parse tree
	 */
	void enterAssemblyAssignment(SolidityParser.AssemblyAssignmentContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#assemblyAssignment}.
	 * @param ctx the parse tree
	 */
	void exitAssemblyAssignment(SolidityParser.AssemblyAssignmentContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#assemblyIdentifierOrList}.
	 * @param ctx the parse tree
	 */
	void enterAssemblyIdentifierOrList(SolidityParser.AssemblyIdentifierOrListContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#assemblyIdentifierOrList}.
	 * @param ctx the parse tree
	 */
	void exitAssemblyIdentifierOrList(SolidityParser.AssemblyIdentifierOrListContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#assemblyIdentifierList}.
	 * @param ctx the parse tree
	 */
	void enterAssemblyIdentifierList(SolidityParser.AssemblyIdentifierListContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#assemblyIdentifierList}.
	 * @param ctx the parse tree
	 */
	void exitAssemblyIdentifierList(SolidityParser.AssemblyIdentifierListContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#assemblyStackAssignment}.
	 * @param ctx the parse tree
	 */
	void enterAssemblyStackAssignment(SolidityParser.AssemblyStackAssignmentContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#assemblyStackAssignment}.
	 * @param ctx the parse tree
	 */
	void exitAssemblyStackAssignment(SolidityParser.AssemblyStackAssignmentContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#labelDefinition}.
	 * @param ctx the parse tree
	 */
	void enterLabelDefinition(SolidityParser.LabelDefinitionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#labelDefinition}.
	 * @param ctx the parse tree
	 */
	void exitLabelDefinition(SolidityParser.LabelDefinitionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#assemblySwitch}.
	 * @param ctx the parse tree
	 */
	void enterAssemblySwitch(SolidityParser.AssemblySwitchContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#assemblySwitch}.
	 * @param ctx the parse tree
	 */
	void exitAssemblySwitch(SolidityParser.AssemblySwitchContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#assemblyCase}.
	 * @param ctx the parse tree
	 */
	void enterAssemblyCase(SolidityParser.AssemblyCaseContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#assemblyCase}.
	 * @param ctx the parse tree
	 */
	void exitAssemblyCase(SolidityParser.AssemblyCaseContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#assemblyFunctionDefinition}.
	 * @param ctx the parse tree
	 */
	void enterAssemblyFunctionDefinition(SolidityParser.AssemblyFunctionDefinitionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#assemblyFunctionDefinition}.
	 * @param ctx the parse tree
	 */
	void exitAssemblyFunctionDefinition(SolidityParser.AssemblyFunctionDefinitionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#assemblyFunctionReturns}.
	 * @param ctx the parse tree
	 */
	void enterAssemblyFunctionReturns(SolidityParser.AssemblyFunctionReturnsContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#assemblyFunctionReturns}.
	 * @param ctx the parse tree
	 */
	void exitAssemblyFunctionReturns(SolidityParser.AssemblyFunctionReturnsContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#assemblyFor}.
	 * @param ctx the parse tree
	 */
	void enterAssemblyFor(SolidityParser.AssemblyForContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#assemblyFor}.
	 * @param ctx the parse tree
	 */
	void exitAssemblyFor(SolidityParser.AssemblyForContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#assemblyIf}.
	 * @param ctx the parse tree
	 */
	void enterAssemblyIf(SolidityParser.AssemblyIfContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#assemblyIf}.
	 * @param ctx the parse tree
	 */
	void exitAssemblyIf(SolidityParser.AssemblyIfContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#assemblyLiteral}.
	 * @param ctx the parse tree
	 */
	void enterAssemblyLiteral(SolidityParser.AssemblyLiteralContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#assemblyLiteral}.
	 * @param ctx the parse tree
	 */
	void exitAssemblyLiteral(SolidityParser.AssemblyLiteralContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#subAssembly}.
	 * @param ctx the parse tree
	 */
	void enterSubAssembly(SolidityParser.SubAssemblyContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#subAssembly}.
	 * @param ctx the parse tree
	 */
	void exitSubAssembly(SolidityParser.SubAssemblyContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#tupleExpression}.
	 * @param ctx the parse tree
	 */
	void enterTupleExpression(SolidityParser.TupleExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#tupleExpression}.
	 * @param ctx the parse tree
	 */
	void exitTupleExpression(SolidityParser.TupleExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#elementaryTypeNameExpression}.
	 * @param ctx the parse tree
	 */
	void enterElementaryTypeNameExpression(SolidityParser.ElementaryTypeNameExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#elementaryTypeNameExpression}.
	 * @param ctx the parse tree
	 */
	void exitElementaryTypeNameExpression(SolidityParser.ElementaryTypeNameExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#numberLiteral}.
	 * @param ctx the parse tree
	 */
	void enterNumberLiteral(SolidityParser.NumberLiteralContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#numberLiteral}.
	 * @param ctx the parse tree
	 */
	void exitNumberLiteral(SolidityParser.NumberLiteralContext ctx);
	/**
	 * Enter a parse tree produced by {@link SolidityParser#identifier}.
	 * @param ctx the parse tree
	 */
	void enterIdentifier(SolidityParser.IdentifierContext ctx);
	/**
	 * Exit a parse tree produced by {@link SolidityParser#identifier}.
	 * @param ctx the parse tree
	 */
	void exitIdentifier(SolidityParser.IdentifierContext ctx);
}