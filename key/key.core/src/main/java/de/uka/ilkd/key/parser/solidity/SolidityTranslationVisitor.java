package de.uka.ilkd.key.parser.solidity;

import org.antlr.v4.runtime.tree.TerminalNode;

import de.uka.ilkd.key.parser.solidity.SolidityParser.ConstructorDefinitionContext;
import de.uka.ilkd.key.parser.solidity.SolidityParser.InheritanceSpecifierContext;

import java.util.*;

public class SolidityTranslationVisitor extends SolidityBaseVisitor<String> {
	// Generated from key.core/src/main/antlr/de/uka/ilkd/key/parser/Solidity.g4 by ANTLR 4.7.1

	private enum FunctionVisibility {
		EXTERNAL, PUBLIC, INTERNAL, PRIVATE
	}

	private enum FieldVisibility {
		PUBLIC, INTERNAL, PRIVATE
	}

	private enum ContractType {
		CONTRACT, INTERFACE, LIBRARY
	}

	private enum ContractStructure {
		CALLABLE_INVOCATION,
		CONSTRUCTOR_BODY,
		CONSTRUCTOR_HEADER, // Note: does not include the list of modifier/parent-constructor calls.
		CONTRACT_DEF,
		ENUM,
		FUNCTION_BODY,
		FUNCTION_HEADER, // Note: does not include the list of modifier calls.
		MODIFIER_BODY,
		MODIFIER_HEADER,
		STRUCT,
		VAR_DECL_LEFT,
		VAR_DECL_RIGHT
	}

	private abstract class SolidityCallable {
		String name;
		String owner;
		String returnType;
		LinkedList<String> argTypes = new LinkedList<>();

		public abstract String visit();

		@Override
		public String toString() {
			String output = returnType + " " + name + "(";
			for (String arg : argTypes)
				output += arg;
			output += ")";
			return output;
		}
	}

	private class SolidityFunction extends SolidityCallable {
		SolidityParser.FunctionDefinitionContext ctx;
		FunctionVisibility visibility;
		boolean isVirtual;
		boolean overrides;

		public String visit() {
			if (ctx != null) {
				return visitFunctionDefinition(ctx);
			} else {
				error("Could not visit the function " + name + " because it is null. CurrentContract: " +
						currentContract.name + ". Owner: " + currentOwnerContract.name);
				return null;
			}
		}
	}

	private class SolidityConstructor extends SolidityCallable {
		SolidityParser.ConstructorDefinitionContext ctx;

		public String visit() {
			if (ctx != null) {
				return visitConstructorDefinition(ctx);
			} else {
				error("Could not visit the constructor " + name + " because it is null. CurrentContract: " +
						currentContract.name + ". Owner: " + currentOwnerContract.name);
				return null;
			}
		}
	}

	private class SolidityModifier extends SolidityCallable {
		SolidityParser.ModifierDefinitionContext ctx;

		public String visit() {
			if (ctx != null) {
				return visitModifierDefinition(ctx);
			} else {
				error("Could not visit the modifier " + name + " because it is null. CurrentContract: " +
						currentContract.name + ". Owner: " + currentOwnerContract.name);
				return null;
			}
		}
	}

	private class SolidityVariable {
		String name;
		String typename;
		boolean isConstant;

		@Override
		public String toString() {
			return typename + " " + name;
		}
	}

	private class SolidityField extends SolidityVariable {
		String owner;
		FieldVisibility visibility;
		SolidityParser.StateVariableDeclarationContext ctx;

		String visit() {
			if (ctx != null) {
				return visitStateVariableDeclaration(ctx);
			} else {
				error("Could not visit the field " + name + " because it is null. CurrentContract: " +
						currentContract.name + ". Owner: " + currentOwnerContract.name);
				return null;
			}
		}
	}

	private class SolidityContract {
		String name;
		ContractType type;
		boolean isAbstract; // TODO
		LinkedList<String> inheritanceList = new LinkedList<>();
		LinkedList<String> c3Linearization = new LinkedList<>();
		LinkedList<SolidityFunction> functions = new LinkedList<>();
		LinkedList<SolidityField> fields = new LinkedList<>();
		LinkedList<SolidityModifier> modifiers = new LinkedList<>();
		SolidityConstructor constructor;

		SolidityFunction getFunction(String funName, List<String> argTypes) {
			for (SolidityFunction fun : functions) {
				if (fun.name.equals(funName) && fun.argTypes.equals(argTypes))
					return fun;
			}
			return null;
		}

		boolean hasFunction(String funName, List<String> argTypes) {
			return getFunction(funName, argTypes) != null;
		}

		SolidityField getField(String fieldName) {
			for (SolidityField field : fields) {
				if (field.name.equals(fieldName))
					return field;
			}
			return null;
		}

		boolean hasField(String fieldName) {
			return getField(fieldName) != null;
		}

		// Note: modifiers cannot be overloaded with different argument lists.
		SolidityModifier getModifier(String modName) {
			for (SolidityModifier mod : modifiers) {
				if (mod.name.equals(modName))
					return mod;
			}
			return null;
		}

		boolean hasModifier(String modName) {
			return getModifier(modName) != null;
		}

		boolean hasNonDefaultConstructor() {
			return constructor != null && constructor.ctx != null;
		}

		@Override
		public String toString() {
			return "Contract " + name + "; \n Inheritance list: " + inheritanceList.toString() +
					"\nlinearization: " + c3Linearization.toString() + "\nFunctions: " +
					functions.toString() + "\nFields: " + fields.toString();
		}
	}

	private class FunctionOverloadResult {
		String mangledName;
		SolidityCallable callable;
		FunctionOverloadResult(String mangledName, SolidityCallable callable) {
			this.mangledName = mangledName; this.callable = callable;
		}
	}

	private class VariableStack {
		private Deque<LinkedList<SolidityVariable>> deque = new ArrayDeque<>();

		public void clear() {
			deque.clear();
		}

		public <T extends SolidityVariable> void pushVar(T var) {
			deque.peekFirst().add(var);

		}
		public void newBlock() {
			deque.addFirst(new LinkedList<>());
		}

		public void newBlock(LinkedList<? extends SolidityVariable> list) {
			deque.add(new LinkedList<>(list));
		}

		public void exitBlock() {
			deque.removeFirst();
		}

		public SolidityVariable getVariableFromIdentifier(String identifier) {
			for (LinkedList<SolidityVariable> scope : deque) {
				for (SolidityVariable var : scope) {
					if (var.name.equals(identifier)) {
						return var;
					}
				}
			}
			return null;
		}

		public String getTypeofIdentifier(String identifier) {
			SolidityVariable var = getVariableFromIdentifier(identifier);
			if (var == null) {
				return null;
			} else {
				return var.typename;
			}
		}

		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder();
			for (LinkedList<SolidityVariable> scope : deque) {
				sb.append('[');
				for (SolidityVariable var : scope) {
					sb.append(var.toString() + ", ");
				}
				sb.append("], ");
			}
			return sb.toString();
		}
	}

	private boolean contractNameExists(String contractName) {
		return contracts.get(contractName) != null;
	}

	// https://docs.soliditylang.org/en/v0.8.12/units-and-global-variables.html
	// TODO: does not include ABI encoding/decoding functions
	List<String> reservedSolidityFunctions = Arrays.asList(
		"addmod", "assert", "blockhash", "call", "delegatecall", "ecrecover", "gasleft", "keccak256", "mulmod",
			"require", "revert", "ripemd160", "selfdestruct", "send", "sha256", "staticcall", "transfer"
	);

    private Map<String,SolidityContract> contracts = new HashMap<>();
	private SolidityContract currentContract; // The contract that we are currently visiting/building
	private SolidityContract currentOwnerContract; // If we are visiting e.g. an inherited function, then this will be the owner

	public String output = "";
	private StringBuilder interfaceOutput = new StringBuilder();

	private VariableStack varStack = new VariableStack();
	private Stack<ContractStructure> structureStack = new Stack<>();

	/**
	 * Construct a mangled name for inherited functions/fields/modifiers. Fields are only mangled if they are private.
	 * @param baseContract The contract that the function/field/modifier was inherited from.
	 * @param identifier The function/field/modifier identifier.
	 * @return A mangled identifier.
	 */
	private String mangleIdentifier(String baseContract, String identifier) {
		return "__" + baseContract + "__" + identifier;
	}

	/**
	 * Checks whether a function identifier is a reserved Solidity function name, e.g., 'require'.
	 * @param function The function identifier.
	 * @return
	 */
	private boolean functionNameIsReserved(String function) {
		return reservedSolidityFunctions.contains(function);
	}

	/**
	 * Checks whether we are currently visiting a function/field/constructor/modifier that was inherited.
	 * @return
	 */
	private boolean currentlyVisitingInheritedMember() {
		return currentContract != currentOwnerContract;
	}

	/**
	 * Constructs a Java interface for the contract that is currently being visited.
	 * This interface contains declarations for all functions that the contract introduces (not overrides), as well as
	 * enums. The resulting Java class for the contract shall 'implement' this interface.
	 * The interface 'extends' all the corresponding interfaces for the contracts in the contract's inheritance list.
	 * @return The Java text output for the interface.
	 */
	private String makeInterface() {
		StringBuilder sb = new StringBuilder();
		sb.append("interface " + currentContract.name);

		// build 'extends' list
		if (currentContract.inheritanceList.size() > 0) {
			sb.append(" extends");
			currentContract.inheritanceList.forEach(c -> {
				sb.append(" " + c + ",");
			});
			sb.deleteCharAt(sb.length()-1);
		}
		sb.append(" {\n");
		sb.append(interfaceOutput.toString());
		sb.append("}\n");
		interfaceOutput = new StringBuilder();
		return sb.toString();
	}

	/**
	 * Make a conversion between a Solidity type and a Java type.
	 * @param solidityTypeName The name of the type in Solidity
	 * @return The name of the type in Java (as it is translated).
	 */
	private String convertType(String solidityTypeName) {
		String javaTypeName = solidityTypeName.replace(" ", "");
		switch (solidityTypeName) {
			case "uint": case "uint256": case "bytes32":
				javaTypeName = "int"; break;
			case "bool"    : javaTypeName = "boolean"; break;
			case "string" : javaTypeName = "String"; break;
			case "address" : javaTypeName = "Address"; break;
			case "address[]" : javaTypeName = "Address[]"; break;
			case "uint[]" : javaTypeName = "int[]"; break;
			case "uint256[]" : javaTypeName = "int[]"; break;
			case "bytes32[]" : javaTypeName = "int[]"; break;
			case "mapping(address=>uint)": javaTypeName="int[]"; break;
			case "mapping(address=>uint256)": javaTypeName="int[]"; break;
			case "mapping(uint=>uint)": javaTypeName="int[]"; break;
			case "mapping(uint256=>uint256)": javaTypeName="int[]"; break;
			case "mapping(uint=>address)": javaTypeName="Address[]"; break;
			case "mapping(uint256=>address)": javaTypeName="Address[]"; break;
			case "mapping(address=>bool)": javaTypeName="boolean[]"; break;
			case "mapping(uint=>bool)": javaTypeName="boolean[]"; break;
			case "mapping(uint256=>bool)": javaTypeName="boolean[]"; break;
			case "mapping(address=>string)": javaTypeName="String[]"; break;
			case "mapping(uint=>string)": javaTypeName="String[]"; break;
			case "mapping(uint256=>string)": javaTypeName="String[]"; break;
			default: break;
		}

		return javaTypeName;
	}

	/**
	 * Resolve a function call; given the function call expression context and from where the function was called,
	 * perform overload resolution to determine which explicit function should be called.
	 * @param ctx The function call expression context.
	 * @return A tuple of 1) the (possibly mangled) name of the explicit function that is called,
	 * and 2) the function itself as a 'SolidityFunction', containing e.g. the context and signature.
	 */
	private FunctionOverloadResult resolveFunctionCall(SolidityParser.FunctionCallExpressionContext ctx) {
		/* We have five different types of "function calls", one of them a constructor call, where overload resolution
		   is not actually done. During overload resolution, we walk up the linearization tree, starting from a
		   given contract (below: Base contract), to find a suitable function. The below table lists whose linearization
		   list we use in which cases, and from where we start walking.
		   Note: s.super.foo() is not allowed.
		   Note: the below does not include calls to modifiers. Those go through 'visitModifierInvocation' instead.
		Type					Example			Linearization owner		Base contract
		super					super.foo()		currentContract			currentOwnerContract; with having to go past it
		external static: 		A.foo()			currentContract			A; without having to go past it. foo must be in A
		external non-static: 	a.foo()			typeof(a)				typeof(a); without having to go past it
		internal				foo()			currentContract			currentOwnContract; without having to go past it
		constructor				A()				does not apply			does not apply
		 */

		String fctName = ctx.expression().getText();
		String comparableName = fctName;
		String contractName = fctName;
		int dotPos = fctName.lastIndexOf('.');
		boolean isExternalCall = dotPos != -1;
		boolean isSuperCall = false;
		boolean isStaticCall = false;
		boolean isConstructorCall = false;
		if (isExternalCall) {
			contractName = fctName.substring(0, dotPos);
			comparableName = fctName.substring(dotPos+1);
			if (contractName.equals("super")) {
				isSuperCall = true;
			} else {
				isStaticCall = contractNameExists(contractName);
			}
		} else {
			// TODO: currently, calls such as "new A()" gets turned into a function call to "newA"
			isConstructorCall = fctName.substring(0, 3).equals("new") && contractNameExists(fctName.substring(3));
		}


		if (isConstructorCall) {
			// Since a contract can have at most one constructor, there is no need to resolve overloads.
			// TODO: currently, calls such as "new A()" gets turned into a function call to "newA"
			SolidityContract ownerContract = contracts.get(fctName.substring(3));
			if (ownerContract == null)
				error("");
			String mangledName = "new " + ownerContract.name + "Impl";
			return new FunctionOverloadResult(mangledName, ownerContract.constructor);
		}

		LinkedList<String> resolvedArgs = new LinkedList<>();
		if (ctx.functionCallArguments().expressionList() != null) {
			for (SolidityParser.ExpressionContext exprCtx : ctx.functionCallArguments().expressionList().expression()) {
				// Get the type of the expression
				SolidityExpressionTypeVisitor typeVisitor = new SolidityExpressionTypeVisitor();
				String typename = typeVisitor.visit(exprCtx);
				resolvedArgs.add(convertType(typename));
			}
		}

		LinkedList<String> linearization;
		String caller; // The owner of the linearization
		if (isExternalCall && !isStaticCall) {
			if (isSuperCall) {
				linearization = currentContract.c3Linearization;
			} else {
				contractName = varStack.getTypeofIdentifier(contractName);
				linearization = contracts.get(contractName).c3Linearization;
			}
			caller = contractName;
		} else {
			linearization = currentContract.c3Linearization;
			caller = currentContract.name;
		}

		String baseContract; // The walking of the linearization list should start from this contract.
		if (isSuperCall || !isExternalCall) {
			baseContract = currentOwnerContract.name;
		} else {
			baseContract = contractName;
		}

		/* When we walk up the linearization list, we must first find the contract 'baseContract',
		   which is from where the actual searching after the function starts.
		   'searchBaseContractForFunction' indicates whether we are allowed to search for the function
		   in 'baseContract', once we locate 'baseContract'.
		 */
		boolean baseContractFound = false;
		boolean searchBaseContractForFunction = true;
		if (isSuperCall) {
			searchBaseContractForFunction = false;
		}

		SolidityFunction resolvedFun = null;
		Iterator<String> reverseIt = linearization.descendingIterator();
		while (reverseIt.hasNext()) {
			String parentName = reverseIt.next();
			if (!baseContractFound) {
				if (parentName.equals(baseContract)) {
					baseContractFound = true;
					if (!searchBaseContractForFunction) {
						continue;
					}
				} else {
					continue;
				}
			}
			SolidityContract parentContract = contracts.get(parentName);
			SolidityFunction fun = parentContract.getFunction(comparableName, resolvedArgs);
			if (fun != null
					&& (fun.visibility != FunctionVisibility.PRIVATE || parentName.equals(caller))) {
				resolvedFun = fun;
				break;
			}
		}

		if (resolvedFun == null) {
			error("Could not resolve function call for function " + comparableName +
					" from contract " + caller);
			return null;
		}

		String mangledName;
		if (isSuperCall) {
			mangledName = mangleIdentifier(resolvedFun.owner, comparableName);
		} else if (isExternalCall) {
			if (isStaticCall) {
				if (resolvedFun.owner.equals(currentContract.name)) {
					mangledName = comparableName;
				} else {
					mangledName = mangleIdentifier(resolvedFun.owner, comparableName);
				}
			} else {
				if (resolvedFun.owner.equals(contractName)) {
					mangledName = fctName;
				} else {
					mangledName = fctName.substring(0, fctName.indexOf('.') + 1) +
							mangleIdentifier(resolvedFun.owner, comparableName);
				}
			}
		} else {
			if (resolvedFun.owner.equals(currentContract.name)) {
				mangledName = fctName;
			} else {
				mangledName = mangleIdentifier(resolvedFun.owner, comparableName);
			}
		}

		return new FunctionOverloadResult(mangledName, resolvedFun);
	}


	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitSourceUnit(SolidityParser.SourceUnitContext ctx) {
		/* First, collect all the contract names, and all their function signatures, modifiers, fields, etc.
		* Then visit the actual contracts (and everything else in the file).
		* This is done so that, if we encounter an instance of a contract type where the contract has not been defined
		* yet, we know that the contract exists.
		* */
		SolidityCollectorVisitor collectorVisitor = new SolidityCollectorVisitor();
		contracts = collectorVisitor.visit(ctx);
		return visitChildren(ctx); 
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitPragmaDirective(SolidityParser.PragmaDirectiveContext ctx) { 
		return visitChildren(ctx); 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitPragmaName(SolidityParser.PragmaNameContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitPragmaValue(SolidityParser.PragmaValueContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitVersion(SolidityParser.VersionContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitVersionOperator(SolidityParser.VersionOperatorContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitVersionConstraint(SolidityParser.VersionConstraintContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitImportDeclaration(SolidityParser.ImportDeclarationContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitImportDirective(SolidityParser.ImportDirectiveContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitContractDefinition(SolidityParser.ContractDefinitionContext ctx) {
		structureStack.push(ContractStructure.CONTRACT_DEF);

		String contractName = ctx.identifier().getText();
		SolidityContract contract = contracts.get(contractName);
		if (contract == null) {
			error("Could not locate the already visited contract " + contractName + ".");
		}
		currentContract = currentOwnerContract = contract;

		varStack.clear();
		for (String parentContractName : currentContract.c3Linearization) {
			SolidityContract parentContract = contracts.get(parentContractName);
			if (parentContract == null) {
				error("Could not locate contract " + parentContractName +
						" as a parent of contract" + currentContract.name);
			}
			varStack.newBlock(parentContract.fields);
		}

		// Create a class/interface from the contract and visit each of its children
        final StringBuffer contractOutput = new StringBuffer();
        if (contract.type == ContractType.CONTRACT) {
			contractOutput.append("class " + contractName + "Impl extends Address implements " + contractName + " {\n");
   		    ctx.contractPart().stream().forEach(part -> contractOutput.append(visit(part) + "\n"));
        } else if (contract.type == ContractType.INTERFACE) {
			contractOutput.append("interface " + contractName);
            if (contract.inheritanceList.size() > 0) {
				contractOutput.append(" extends");
				contract.inheritanceList.forEach(c -> contractOutput.append(" " + c + ","));
				contractOutput.setCharAt(contractOutput.length()-1,' ');
            }
			contractOutput.append(" {\n");
   		    ctx.contractPart().stream().forEach(part -> contractOutput.append(visit(part) + ";\n"));
        } else if (contract.type == ContractType.LIBRARY) {
			contractOutput.append("class " + contractName + " {\n");
   		    ctx.contractPart().stream().forEach(part -> contractOutput.append(visit(part) + "\n"));
        } else {
			error("Unrecognized contract type for contract " + contractName + " encountered.");
		}

		/* Import all inherited functions, fields, modifiers, and constructors from the contract's parents.
		   Inherited functions and modifiers are renamed according to the 'mangleIdentifier' function.
		   Fields are only renamed if they are private. Super calls are also replaced with calls to explicit functions.
		 */
		for (String parentName : contract.c3Linearization) {
			if (parentName.equals(currentContract.name))
				continue;

			SolidityContract parent = contracts.get(parentName);
			if (parent == null)
				error("Could not locate parent contract " + parentName + " to " + currentContract.name);
			currentOwnerContract = parent;

			// The variable stack shall contain all fields from the parent and the ones that it inherits.
			varStack.clear();
			for (String parentParentName : parent.c3Linearization) {
				SolidityContract parentParent = contracts.get(parentParentName);
				if (parentParent == null) {
					error("Could not locate contract " + parentParentName +
							" as a parent of contract" + currentContract.name);
				}
				varStack.newBlock(parentParent.fields);
			}

			// Import fields
			if (parent.fields == null)
				error("Could not locate parent contract " + parentName + " to " +
						currentContract.name + " when importing inherited fields.");
			parent.fields.forEach(field -> contractOutput.append(field.visit() + '\n'));

			// Import functions
			if (parent.functions == null)
				error("Could not locate parent contract " + parentName + " to " +
						currentContract.name + " when importing inherited functions.");
			parent.functions.forEach(fun -> contractOutput.append(fun.visit() + '\n'));

			// Import modifiers
			if (parent.modifiers == null)
				error("Could not locate parent contract " + parentName + " to " +
						currentContract.name + " when importing inherited modifiers.");
			parent.modifiers.forEach(mod -> contractOutput.append(mod.visit() + '\n'));

			// Import constructors (as functions). Each base class can have at most one constructor.
			if (parent.hasNonDefaultConstructor())
				contractOutput.append(parent.constructor.visit() + '\n');
		}

		// For contracts, an interface is created in addition to the flattened contract, so that type information
		// from the inheritance hierarchy is kept.
        if (contract.type == ContractType.CONTRACT) {
            output += makeInterface();
        } 
        output += contractOutput.append("}\n").toString();

		structureStack.pop();

		return getOutput();
	}

	private String error(String string) throws RuntimeException {
		throw new RuntimeException(string);
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitInheritanceSpecifier(SolidityParser.InheritanceSpecifierContext ctx) { 
		return visitChildren(ctx); 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitContractPart(SolidityParser.ContractPartContext ctx) { 
		return visitChildren(ctx); 
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitStateVariableDeclaration(SolidityParser.StateVariableDeclarationContext ctx) {
		structureStack.push(ContractStructure.VAR_DECL_LEFT);

		SolidityField field = currentOwnerContract.getField(ctx.identifier().getText());

		String output = "  ";

		switch (field.visibility) {
			case PUBLIC: output += "public"; break;
			case PRIVATE: output += "private"; break;
			// The default visibility is "internal", roughly corresponding to java's "protected".
			default: output += "protected"; break;
		}
		if (field.isConstant) {
			output += "final";
		}

		String mangledName = String.valueOf(field.name);
		if (currentlyVisitingInheritedMember() && field.visibility == FieldVisibility.PRIVATE) {
			mangledName = mangleIdentifier(currentOwnerContract.name, mangledName);
		}

		String shownTypename = String.valueOf(field.typename);
		if (contractNameExists(field.typename))
			shownTypename += "Impl";

		output += " " + shownTypename + " " + mangledName;

		structureStack.pop();
		structureStack.push(ContractStructure.VAR_DECL_RIGHT);

		if (ctx.expression() != null && !ctx.expression().isEmpty()) {
			output += " = " + visit(ctx.expression());
		}

		structureStack.pop();

		return output + ";"; 
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitUsingForDeclaration(SolidityParser.UsingForDeclarationContext ctx) { return visitChildren(ctx); }

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitStructDefinition(SolidityParser.StructDefinitionContext ctx) {
		structureStack.push(ContractStructure.STRUCT);
		StringBuffer structDef = new StringBuffer("static class "+visit(ctx.identifier()) + "{\n");
		ctx.variableDeclaration().stream().forEach(v -> structDef.append(visit(v)).append(";\n"));
		structDef.append("}");
		structureStack.pop();
		return structDef.toString(); 
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitConstructorDefinition(SolidityParser.ConstructorDefinitionContext ctx) {
		structureStack.push(ContractStructure.CONSTRUCTOR_HEADER);
		varStack.newBlock();

		String visibility;
		if (currentlyVisitingInheritedMember()) {
			// "Inherit" the constructor by constructing a new private function representing its body and modifiers.
			visibility = "private";
		} else {
			visibility = "public"; // Note: constructors in Solidity are always public (as of now)
		}

		StringBuffer parameters = new StringBuffer("Message msg,");
		ctx.parameterList().parameter().stream().forEach(param -> 
		parameters.append(visit(param) + ","));
		if (parameters.length() > 0) { 
			parameters.deleteCharAt(parameters.length() - 1);
		}

		structureStack.pop();
		structureStack.push(ContractStructure.CONSTRUCTOR_BODY);

		/* A constructor definition can have calls to parent constructors in its header.
		   Each one shall be an instance of the below class.
		   Note that the parser treats such an invocation as a "ModifierInvocation".
		   The constructor can also have calls to actual modifiers.
		   All of these invocations will exist as normal "function calls" at the top of the body of the constructor output.
		 */
		class ConstructorInvocation {
			String name;
			int inheritanceListPos;
			SolidityParser.ModifierInvocationContext ctx;
			ConstructorInvocation(String name, int inheritanceListPos, SolidityParser.ModifierInvocationContext ctx) {
				this.name = name; this.inheritanceListPos = inheritanceListPos; this.ctx = ctx;
			}
		}

		StringBuffer modsOutput = new StringBuffer();
		if (!ctx.modifierList().modifierInvocation().isEmpty()) {
			// A constructor "modifier" may be a call to a parent constructor, or to an actual modifier. Collect those.
			LinkedList<ConstructorInvocation> constructorCalls = new LinkedList<>();
			LinkedList<SolidityParser.ModifierInvocationContext> modCalls = new LinkedList<>();
			ctx.modifierList().modifierInvocation().forEach(mod -> {
				String identifier = visit(mod.identifier());
				List<String> inheritanceList = currentOwnerContract.inheritanceList;
				// Check whether the identifier is a modifier or a constructor
				int inheritanceListPos = inheritanceList.indexOf(identifier);
				if (inheritanceListPos == -1) { // A modifier invocation
					modCalls.add(mod);
				} else { // A (parent) constructor invocation
					ConstructorInvocation invocation = new ConstructorInvocation(identifier, inheritanceListPos, mod);
					// The parent constructor calls shall be inserted as "function calls" in the constructor body.
					// However, these should be called in the order of the contract's inheritance list.
					// Determine where the constructor should be inserted.
					int insertPos = 0;
					for (ConstructorInvocation c : constructorCalls) {
						if (inheritanceListPos < c.inheritanceListPos)
							break;
						insertPos++;
					}
					constructorCalls.add(insertPos, invocation);
				}
			});
			// TODO: should modifiers or constructor invocations be visited first?
			modCalls.forEach(mod -> modsOutput.append(visit(mod) + ";\n"));
			constructorCalls.forEach(constructor -> modsOutput.append(visit(constructor.ctx) + ";\n"));
		}

		StringBuffer body = new StringBuffer(visit(ctx.block()));
		if (modsOutput.length() > 0) body.insert(body.indexOf("{") + 1, "\n" + modsOutput);

		varStack.exitBlock();
		structureStack.pop();

		return visibility + " " + currentOwnerContract.name + "Impl(" + parameters + ")" + body;
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitModifierDefinition(SolidityParser.ModifierDefinitionContext ctx) {
		structureStack.push(ContractStructure.MODIFIER_HEADER);
		varStack.newBlock();

		SolidityModifier modifier = currentOwnerContract.getModifier(ctx.identifier().getText());

		String mangledName = String.valueOf(modifier.name);
		if (currentlyVisitingInheritedMember()) {
			mangledName = mangleIdentifier(currentOwnerContract.name, mangledName);
		}

		String visibility = "private"; // Modifiers are always private

		StringBuffer parameters = new StringBuffer("Message msg,");
		if (ctx.parameterList() != null) {
			ctx.parameterList().parameter().stream().forEach(param -> 
				parameters.append(visit(param) + ","));
		}
		if (parameters.length() > 0) parameters.deleteCharAt(parameters.length() - 1);
		String returnType = ctx.getParent() instanceof ConstructorDefinitionContext ? "" : "void";

		structureStack.pop();

		structureStack.push(ContractStructure.MODIFIER_BODY);
		String bodyOutput = visit(ctx.block());
		structureStack.pop();
		varStack.exitBlock();

		return visibility + " " + returnType + " " + mangledName + "(" + parameters + ")" + bodyOutput;
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitModifierInvocation(SolidityParser.ModifierInvocationContext ctx) {
		structureStack.push(ContractStructure.CALLABLE_INVOCATION);

		String modName = visit(ctx.identifier());
		boolean isConstructorCall = currentOwnerContract.inheritanceList.contains(modName);
		if (isConstructorCall) {
			// hack: if "modifier" is really a parent constructor
            modName += "Impl";
        } else if (!currentContract.hasModifier(modName)) {
			SolidityContract parentWithModifier = null;
			Iterator<String> it = currentContract.c3Linearization.descendingIterator();
			while (it.hasNext()) {
				SolidityContract parent = contracts.get(it.next());
				if (parent.hasModifier(modName)) {
					parentWithModifier = parent;
					break;
				}
			}
			if (parentWithModifier == null) {
				error("Call to modifier " + modName + " was made in the constructor of contract " +
						currentContract.name + ", but no parent of " + currentContract.name + "defines " + modName);
			} else {
				modName = mangleIdentifier(parentWithModifier.name, modName);
			}
		}

		StringBuffer arguments = new StringBuffer("msg");

		if (ctx.expressionList() != null && !ctx.expressionList().isEmpty()) {			
			ctx.expressionList().expression().stream()
			.forEach(elt -> arguments.append("," + visit(elt)));
		}

		structureStack.pop();

		return modName + "(" + arguments + ")";
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitFunctionDefinition(SolidityParser.FunctionDefinitionContext ctx) {
		structureStack.push(ContractStructure.FUNCTION_HEADER);
		varStack.newBlock();

		String funName = ctx.identifier().getText();
		LinkedList<String> argTypes = new LinkedList<>();
		ctx.parameterList().parameter().forEach(parameter -> argTypes.add(visit(parameter.typeName())));
		SolidityFunction function = currentOwnerContract.getFunction(funName, argTypes);

		String modifier = "";
		switch (function.visibility) {
			case PUBLIC: modifier = "public"; break;
			case PRIVATE: modifier = "private"; break;
			default: break;
		}

		String mangledName = String.valueOf(function.name);
		if (currentlyVisitingInheritedMember()) {
			mangledName = mangleIdentifier(currentOwnerContract.name, mangledName);
		}

		StringBuffer parameters;
		switch(mangledName) {
		case "require":case "assert": 
			parameters = new StringBuffer();
			break;
		default: parameters = new StringBuffer("Message msg,");		
		}
		
		ctx.parameterList().parameter().stream().forEach(param -> 
			parameters.append(visit(param) + ","));

		if (parameters.length() > 0)
			parameters.deleteCharAt(parameters.length() - 1);

		String returnType = convertType(function.returnType);

		structureStack.pop();
		structureStack.push(ContractStructure.FUNCTION_BODY);

		StringBuffer mods = new StringBuffer();

		ctx.modifierList().modifierInvocation().stream().
		forEach(inv -> mods.append(visit(inv) + ";\n"));
        
        StringBuffer body = new StringBuffer();
        if (ctx.block() != null) {
    		body = new StringBuffer(visit(ctx.block()));
    		if (mods.length() > 0) body.insert(body.indexOf("{") + 1, "\n" + mods);
        }

        String fctHeader = modifier + (currentContract.type == ContractType.LIBRARY ? " static " : " ")
            + returnType + " " + mangledName + "(" + parameters + ")";

		if (!currentlyVisitingInheritedMember() && !function.overrides)
			interfaceOutput.append(fctHeader + ";\n");

		varStack.exitBlock();
		structureStack.pop();

		return fctHeader + " " + body;
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitReturnParameters(SolidityParser.ReturnParametersContext ctx) { 
		return visitChildren(ctx); 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitModifierList(SolidityParser.ModifierListContext ctx) { 
		return visitChildren(ctx); 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitEventDefinition(SolidityParser.EventDefinitionContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitEnumValue(SolidityParser.EnumValueContext ctx) { 
		return visitChildren(ctx); 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitEnumDefinition(SolidityParser.EnumDefinitionContext ctx) {
		structureStack.push(ContractStructure.ENUM);
		StringBuffer enumDef = new StringBuffer("enum ");
		enumDef.append(visit(ctx.identifier()));
		enumDef.append("{");
		ctx.enumValue().stream().forEach(v -> enumDef.append(visit(v.identifier())+","));		
		enumDef.deleteCharAt(enumDef.length()-1);
		enumDef.append("}");
		// The enum output is not added to the java class, but rather, the java interface for the contract
		interfaceOutput.append(enumDef.toString() + '\n');
		structureStack.pop();
		return "";
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitParameterList(SolidityParser.ParameterListContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitParameter(SolidityParser.ParameterContext ctx) {
		String typename = visit(ctx.typeName());
		String identifier = visit(ctx.identifier());
		SolidityVariable var = new SolidityVariable();
		var.typename = typename;
		var.name = identifier;
		varStack.pushVar(var);
		return typename + " " + identifier;
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override 
	public String visitEventParameterList(SolidityParser.EventParameterListContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override 
	public String visitEventParameter(SolidityParser.EventParameterContext ctx) { return visitChildren(ctx); }

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override 
	public String visitFunctionTypeParameterList(SolidityParser.FunctionTypeParameterListContext ctx) { return visitChildren(ctx); }

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override 
	public String visitFunctionTypeParameter(SolidityParser.FunctionTypeParameterContext ctx) { 
		return visitChildren(ctx); 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override 
	public String visitVariableDeclaration(SolidityParser.VariableDeclarationContext ctx) {
		String identifier = visit(ctx.identifier());
		String typename = visit(ctx.typeName());
		SolidityVariable var = new SolidityVariable();
		var.name = identifier;
		var.typename = typename;
		varStack.pushVar(var);

		String mangledName = typename;
		if (contractNameExists(typename)) // If it is a contract type
			mangledName += "Impl";

		return mangledName + " " + identifier;
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitTypeName(SolidityParser.TypeNameContext ctx) { 
		return convertType(ctx.getText());
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitUserDefinedTypeName(SolidityParser.UserDefinedTypeNameContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitMapping(SolidityParser.MappingContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitFunctionTypeName(SolidityParser.FunctionTypeNameContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitStorageLocation(SolidityParser.StorageLocationContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitStateMutability(SolidityParser.StateMutabilityContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitBlock(SolidityParser.BlockContext ctx) { 
		StringBuffer output = new StringBuffer("{");
		varStack.newBlock();
		ctx.statement().stream().forEach(stmnt -> output.append("\n" + visit(stmnt)));
		varStack.exitBlock();
		return output.append("\n}").toString();
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitStatement(SolidityParser.StatementContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitPlaceHolderStatement(SolidityParser.PlaceHolderStatementContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitExpressionStatement(SolidityParser.ExpressionStatementContext ctx) { 
		return visit(ctx.expression()) + ";"; 
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitIfStatement(SolidityParser.IfStatementContext ctx) { 			
		String condition = visit(ctx.expression());
		String _then = visit(ctx.statement(0));
		String output = "if (" + condition + ") " + _then;

		if (ctx.statement().size() > 1) {
			String _else = visit(ctx.statement(1));
			output += _else;  
		}

		return output; 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitWhileStatement(SolidityParser.WhileStatementContext ctx) { 
		String condition = visit(ctx.expression());
		String body = visit(ctx.statement());
		String output = "while ( " + condition + " ) " + body;

		return output; 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitSimpleStatement(SolidityParser.SimpleStatementContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitForStatement(SolidityParser.ForStatementContext ctx) { 
		StringBuffer result = new StringBuffer("for (");
		String decl = visit(ctx.simpleStatement());
		String guard = visit(ctx.expression(0));
	
		String update = visit(ctx.expression(1));
		String body = visit(ctx.statement());
		
		return result.append(decl).
				append(guard).append(";").
				append(update).append(")").append("{").
										   append(body).
										   append("}").toString(); 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitInlineAssemblyStatement(SolidityParser.InlineAssemblyStatementContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitDoWhileStatement(SolidityParser.DoWhileStatementContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitContinueStatement(SolidityParser.ContinueStatementContext ctx) { 
		return "continue;"; 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitBreakStatement(SolidityParser.BreakStatementContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitReturnStatement(SolidityParser.ReturnStatementContext ctx) { 
		return "return " + (ctx.expression() == null ? ";" : visit(ctx.expression())+";");
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitThrowStatement(SolidityParser.ThrowStatementContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitEmitStatement(SolidityParser.EmitStatementContext ctx) { 
		return ";"; 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitVariableDeclarationStatement(SolidityParser.VariableDeclarationStatementContext ctx) {
		structureStack.push(ContractStructure.VAR_DECL_LEFT);
		String decl = this.visit(ctx.variableDeclaration());
		structureStack.pop();

		if (ctx.variableDeclaration() != null) { // If it is a declaration of one variable...
			if (ctx.expression() != null){
				structureStack.push(ContractStructure.VAR_DECL_RIGHT);
				decl = decl + "=" + this.visit(ctx.expression());
				structureStack.pop();
			}
			return decl + ";";
		}
		else { // If it is a list of identifiers...
			// TODO
		}
		return "//" + ctx.getText();
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitVariableDeclarationList(SolidityParser.VariableDeclarationListContext ctx) { 
		return visitChildren(ctx); 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitIdentifierList(SolidityParser.IdentifierListContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitElementaryTypeName(SolidityParser.ElementaryTypeNameContext ctx) { 
		return convertType(ctx.getText()); 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitAdditiveExpression(SolidityParser.AdditiveExpressionContext ctx) { 
		return visit(ctx.expression(0)) + ctx.binop.getText() + visit(ctx.expression(1)); 
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitTildeExpression(SolidityParser.TildeExpressionContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitNotExpression(SolidityParser.NotExpressionContext ctx) { 
		return "!"+visit(ctx.expression()); 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitParenExpression(SolidityParser.ParenExpressionContext ctx) { 
		return "(" + visit(ctx.expression()) + ")"; 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitPreIncOrDecExpression(SolidityParser.PreIncOrDecExpressionContext ctx) { 
		return (ctx.unop == ctx.INC() ? "++" : "--") + visit(ctx.expression());
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitLogicalShiftExpression(SolidityParser.LogicalShiftExpressionContext ctx) { 		
		return error("Logical Shift unsupported"); 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitPostIncOrDecExpression(SolidityParser.PostIncOrDecExpressionContext ctx) { 
		return visit(ctx.expression()) + (ctx.unop == ctx.INC() ? "++" : "--");
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitAndExpression(SolidityParser.AndExpressionContext ctx) { 
		return visit(ctx.expression(0)) + "&&" + visit(ctx.expression(1)); 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitCompExpression(SolidityParser.CompExpressionContext ctx) { 
		String expr1 = visit(ctx.expression(0));
		String expr2 = visit(ctx.expression(1));

		return expr1 + ctx.binop.getText() + expr2;
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitBitwiseAndExpression(SolidityParser.BitwiseAndExpressionContext ctx) { 
		return visit(ctx.expression(0)) + "&" + visit(ctx.expression(1)); 
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitFunctionCallExpression(SolidityParser.FunctionCallExpressionContext ctx) {
		String fctName = visit(ctx.expression());
		String mangledName = fctName;
		if (!functionNameIsReserved(fctName)) {
			FunctionOverloadResult overload = resolveFunctionCall(ctx);
			mangledName = overload.mangledName;
		}

		StringBuffer arguments;
        boolean skip = false;
		switch(mangledName) {
        case "require2":
            arguments = new StringBuffer("(int)sender != 0,");
			mangledName = "require";
            skip = true;
            break;
        case "require3":
            arguments = new StringBuffer("(int)recipient != 0,");
			mangledName = "require";
            skip = true;
            break;
		case "require":case "assert":case "push":
			arguments = new StringBuffer();
			break;
		default: arguments = new StringBuffer("msg,");		
		}

		if (!skip && ctx.functionCallArguments() != null && !ctx.functionCallArguments().isEmpty()) {
			if (ctx.functionCallArguments().expressionList()!= null && 
					!ctx.functionCallArguments().expressionList().isEmpty()) {
				ctx.functionCallArguments().expressionList().expression().stream()
				.forEach(elt -> arguments.append(visit(elt)+","));
			}
		}
		arguments.deleteCharAt(arguments.length() - 1);

		return mangledName + "(" + arguments + ")";
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitPrimaryExprExpression(SolidityParser.PrimaryExprExpressionContext ctx) { 
		return visitChildren(ctx); 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitBitwiseXorExpression(SolidityParser.BitwiseXorExpressionContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitDotExpression(SolidityParser.DotExpressionContext ctx) { 
		String exp = visit(ctx.expression());
        String ident = visit(ctx.identifier());
        return exp + "." + ident;
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitUnaryAdditiveExpression(SolidityParser.UnaryAdditiveExpressionContext ctx) { 
		return visitChildren(ctx); 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitNewTypeNameExpression(SolidityParser.NewTypeNameExpressionContext ctx) {
		var result = visitChildren(ctx);
		return result;
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitAssignmentExpression(SolidityParser.AssignmentExpressionContext ctx) { 
		if (ctx.binop.getText().equals("=")) {
			return this.visit(ctx.expression(0)) + " = " + this.visit(ctx.expression(1));
		} else if (ctx.binop.getText().equals("+=")) { 
			return this.visit(ctx.expression(0)) + " += " + this.visit(ctx.expression(1));
		} else if (ctx.binop.getText().equals("-=")) { 
			return this.visit(ctx.expression(0)) + " -= " + this.visit(ctx.expression(1));
		} else {
			error("Unsupported assignment operation " + ctx.binop.getText());			
		}
		return "Unsupported assignment operation";
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitMultiplicativeExpression(SolidityParser.MultiplicativeExpressionContext ctx) { 
		return visit(ctx.expression(0)) + ctx.binop.getText() + visit(ctx.expression(1)); 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitOrExpression(SolidityParser.OrExpressionContext ctx) { 
		return visit(ctx.expression(0)) + "||" + visit(ctx.expression(1)); 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitPowerExpression(SolidityParser.PowerExpressionContext ctx) { 
		error("Power expression not supported");
		return "error"; 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitBitwiseOrExpression(SolidityParser.BitwiseOrExpressionContext ctx) { 
		return visit(ctx.expression(0)) + "|" + visit(ctx.expression(1)); 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitArrayAccessExpression(SolidityParser.ArrayAccessExpressionContext ctx) { 
		return visit(ctx.expression(0))+"[(int)"+visit(ctx.expression(1))+"]";
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitDeleteExpression(SolidityParser.DeleteExpressionContext ctx) { 
		error("Delete expression not supported");
		return "error";	
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitEqualityExpression(SolidityParser.EqualityExpressionContext ctx) { 
		return visit(ctx.expression(0)) + ctx.binop.getText() + visit(ctx.expression(1)); 
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitTernaryExpression(SolidityParser.TernaryExpressionContext ctx) { 
		return visit(ctx.expression(0)) + "?" + visit(ctx.expression(1)) + ":" + visit(ctx.expression(2)); 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitPrimaryExpression(SolidityParser.PrimaryExpressionContext ctx) { 
		if (ctx.BooleanLiteral() != null) 
			return ctx.BooleanLiteral().getText();
		else if (ctx.identifier() != null)
			return visit(ctx.identifier());

		return visitChildren(ctx); 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitExpressionList(SolidityParser.ExpressionListContext ctx) {
		return visitChildren(ctx);
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitNameValueList(SolidityParser.NameValueListContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitNameValue(SolidityParser.NameValueContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitFunctionCallArguments(SolidityParser.FunctionCallArgumentsContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitFunctionCall(SolidityParser.FunctionCallContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitAssemblyBlock(SolidityParser.AssemblyBlockContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitAssemblyItem(SolidityParser.AssemblyItemContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitAssemblyExpression(SolidityParser.AssemblyExpressionContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitAssemblyCall(SolidityParser.AssemblyCallContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitAssemblyLocalDefinition(SolidityParser.AssemblyLocalDefinitionContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitAssemblyAssignment(SolidityParser.AssemblyAssignmentContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitAssemblyIdentifierOrList(SolidityParser.AssemblyIdentifierOrListContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitAssemblyIdentifierList(SolidityParser.AssemblyIdentifierListContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitAssemblyStackAssignment(SolidityParser.AssemblyStackAssignmentContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitLabelDefinition(SolidityParser.LabelDefinitionContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitAssemblySwitch(SolidityParser.AssemblySwitchContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitAssemblyCase(SolidityParser.AssemblyCaseContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitAssemblyFunctionDefinition(SolidityParser.AssemblyFunctionDefinitionContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitAssemblyFunctionReturns(SolidityParser.AssemblyFunctionReturnsContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitAssemblyFor(SolidityParser.AssemblyForContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitAssemblyIf(SolidityParser.AssemblyIfContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitAssemblyLiteral(SolidityParser.AssemblyLiteralContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitSubAssembly(SolidityParser.SubAssemblyContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitTupleExpression(SolidityParser.TupleExpressionContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitElementaryTypeNameExpression(SolidityParser.ElementaryTypeNameExpressionContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitNumberLiteral(SolidityParser.NumberLiteralContext ctx) { 
		return ctx.DecimalNumber().getText() + "L"; 
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitIdentifier(SolidityParser.IdentifierContext ctx) {
		String identifier = ctx.getText();

		/* If the identifier is of a private field that has been inherited, then this should be mangled.
		   This is because a subcontract may define a field with the same identifier.
		   However, the flattened contract shall contain both of these fields.
		   The name should not be mangled if resides in a definition where a new name is introduces, e.g.,
		   the header of a function/modifier/constructor definition, or on the left side of the '=' in a
		   variable declaration.
		 */
		boolean mangleIdentThatIsInheritedPrivateField = false;
		if (currentlyVisitingInheritedMember()) {
			switch (structureStack.peek()) {
				case CALLABLE_INVOCATION:
				case CONSTRUCTOR_BODY:
				case FUNCTION_BODY:
				case MODIFIER_BODY:
				case VAR_DECL_RIGHT:
					mangleIdentThatIsInheritedPrivateField = true;
					break;
				default:
					break;
			}

			if (mangleIdentThatIsInheritedPrivateField) {
				SolidityVariable var = varStack.getVariableFromIdentifier(identifier);
				if (var != null && var instanceof SolidityField) {
					SolidityField field = (SolidityField)var;
					if (field.visibility == FieldVisibility.PRIVATE &&
							!field.owner.equals(currentContract.name)) {
						identifier = mangleIdentifier(field.owner, identifier);
					}
				}
			}
		}
		return identifier;
	}

	@Override public String visitTerminal(TerminalNode n) {
		return "// " + n.getText();

	}

	public String getOutput() {
		return output;
	}

	/* This visitor is used to collect all the contracts and their functions/fields/modifiers/constructors that
	   are within the input file, before the bodies of these are actually visited to produce the Java text output.
	   This is so that, e.g., if a function calls another function that is defined after the former function,
	   that function can know that the latter function exists.
	   In addition, we also construct C3 linearizations of the inheritance hierarchy within the input file.
	 */
	private class SolidityCollectorVisitor extends SolidityBaseVisitor<HashMap<String, SolidityContract>> {
		HashMap<String, SolidityContract> contracts = new HashMap<>();
		SolidityContract currentContract;
		SolidityFunction currentFunction;

		@Override
		public HashMap<String, SolidityContract> visitSourceUnit(SolidityParser.SourceUnitContext ctx) {
			ctx.contractDefinition().forEach(contract -> visit(contract));
			return contracts;
		}

		@Override
		public HashMap<String, SolidityContract> visitContractDefinition(SolidityParser.ContractDefinitionContext ctx) {
			String contractName = ctx.identifier().getText();
			if (contractNameExists(contractName)) {
				error("Contract redefinition; there exists multiple definitions of the contract " + contractName);
			}
			SolidityContract contract = new SolidityContract();
			currentContract = contract;
			contracts.put(contractName, contract);
			contract.name = contractName;
			if (ctx.ContractKeyword() != null) {
				contract.type = ContractType.CONTRACT;
			} else if (ctx.InterfaceKeyword() != null) {
				contract.type = ContractType.INTERFACE;
			} else if (ctx.LibraryKeyword() != null) {
				contract.type = ContractType.LIBRARY;
			} else {
				error("No valid contract type found for contract " + contractName);
			}

			for (InheritanceSpecifierContext ictx : ctx.inheritanceSpecifier()) {
				contract.inheritanceList.add(ictx.getText());
			}
			constructC3Linearization(contract);
			if (contract.c3Linearization == null)
				error("Could not construct the C3 linearization for contract " + contractName);

			ctx.contractPart().forEach(part -> visit(part));

			// If a constructor was not defined, make a default one.
			if (contract.constructor == null) {
				SolidityConstructor constructor = new SolidityConstructor();
				contract.constructor = constructor;
				constructor.name = constructor.owner = constructor.returnType = contract.name;
				constructor.argTypes = new LinkedList<>();
			}

			return contracts;
		}

		@Override
		public HashMap<String, SolidityContract> visitFunctionDefinition(SolidityParser.FunctionDefinitionContext ctx) {
			SolidityFunction function = new SolidityFunction();
			currentContract.functions.add(function);
			currentFunction = function;
			String fctName = ctx.identifier() == null ? "fallback" : ctx.identifier().getText();
			function.ctx = ctx;
			function.name = fctName;
			function.owner = currentContract.name;

			function.returnType = ctx.getParent() instanceof ConstructorDefinitionContext ? "" : "void";
			if (ctx.returnParameters() != null && !ctx.returnParameters().isEmpty()) {
				function.returnType = ctx.returnParameters().parameterList().parameter(0).typeName().getText();
			}

			function.isVirtual = !ctx.modifierList().VirtualKeyword().isEmpty();
			function.overrides = !ctx.modifierList().OverrideKeyword().isEmpty();
			if (!ctx.modifierList().PublicKeyword().isEmpty()) {
				function.visibility = FunctionVisibility.PUBLIC;
			} else if (!ctx.modifierList().ExternalKeyword().isEmpty()) {
				function.visibility = FunctionVisibility.EXTERNAL;
			} else if (!ctx.modifierList().InternalKeyword().isEmpty()) {
				function.visibility = FunctionVisibility.INTERNAL;
			} else if (!ctx.modifierList().PrivateKeyword().isEmpty()) {
				function.visibility = FunctionVisibility.PRIVATE;
			} else {
				error("No visibility specifier found for function " + fctName +
						" in contract " + currentContract.name);
			}

			ctx.parameterList().parameter().forEach(param -> visit(param));

			return contracts;
		}

		@Override
		public HashMap<String, SolidityContract> visitModifierDefinition(SolidityParser.ModifierDefinitionContext ctx) {
			SolidityModifier modifier = new SolidityModifier();
			currentContract.modifiers.add(modifier);
			String modName = ctx.identifier() == null ? "fallback" : ctx.identifier().getText();
			modifier.name = modName;
			modifier.ctx = ctx;
			// Note: there is no need to collect the argument types for the modifier, as modifiers cannot be overloaded.
			// Also, their visibility cannot be specified (they are always private).
			return contracts;
		}

		@Override
		public HashMap<String, SolidityContract> visitStateVariableDeclaration(SolidityParser.StateVariableDeclarationContext ctx) {
			SolidityField field = new SolidityField();
			currentContract.fields.add(field);
			field.ctx = ctx;
			field.name = ctx.identifier().getText();
			field.owner = currentContract.name;
			field.typename = convertType(ctx.typeName().getText());

			if (!ctx.PublicKeyword().isEmpty()) {
				field.visibility = FieldVisibility.PUBLIC;
			} else if (!ctx.InternalKeyword().isEmpty()) {
				field.visibility = FieldVisibility.INTERNAL;
			} else if (!ctx.PrivateKeyword().isEmpty()) {
				field.visibility = FieldVisibility.PRIVATE;
			} else { // The default visibility is "internal"
				field.visibility = FieldVisibility.INTERNAL;
			}
			field.isConstant = !ctx.ConstantKeyword().isEmpty();

			return contracts;
		}

		@Override
		public HashMap<String, SolidityContract> visitConstructorDefinition(SolidityParser.ConstructorDefinitionContext ctx) {
			if (currentContract.hasNonDefaultConstructor())
				error("Cannot define more than one constructor for contract " + currentContract.name);
			SolidityConstructor constructor = new SolidityConstructor();
			currentContract.constructor = constructor;
			constructor.ctx = ctx;
			constructor.name = constructor.owner = constructor.returnType = currentContract.name;
			// As of now, there is no need to determine the arg types for the constructor. No constructor overloading
			// is done, since a contract only can contain at most one constructor.
			return contracts;
		}

		@Override
		public HashMap<String, SolidityContract> visitParameter(SolidityParser.ParameterContext ctx) {
			String typename = convertType(ctx.typeName().getText());
			currentFunction.argTypes.add(typename);
			return contracts;
		}

		/**
		 * Constructs the C3 linearization for 'contract', which is a list of contracts that the contract
		 * inherits from, from least derived to most derived, including the contract itself at the end.
		 * In other words, it is a flattening of the contract's inheritance tree structure.
		 * @param contract
		 * @return The contract's C3 linearization as a list of contracts, from least derived to most derived.
		 */
		private void constructC3Linearization(SolidityContract contract) {
			// If the inheritance list is empty, the linearization is just the contract itself.
			if (contract.inheritanceList.isEmpty()) {
				contract.c3Linearization = new LinkedList<String>(Collections.singleton(contract.name));
			} else {
				// Construct the list of lists that is to be sent to the 'merge' function.
				// It contains the linearizations of all contracts in the inheritance list + the inheritance list itself.
				LinkedList<LinkedList<String>> baseLinearizations = new LinkedList<>();
				for (String base : contract.inheritanceList) {
					if (base.equals(contract.name)) {
						error("A contract may not inherit from itself.");
					}
					LinkedList<String> baseLinearization = contracts.get(base).c3Linearization;
					if (baseLinearization == null) {
						error("The contract inherits from something not defined yet");
					}
					// Create a copy so that, when 'baseLinearizations' is mutated by merge(), 'linearizations' is not mutated.
					baseLinearizations.addFirst(new LinkedList<>(baseLinearization));
				}
				// Copy the inheritance list, put the contract at the end of it, and put it in the merge input list
				LinkedList<String> inheritanceList = new LinkedList<>(contract.inheritanceList);
				inheritanceList.addLast(contract.name);
				baseLinearizations.addLast(inheritanceList);
				// Perform the 'merge' operation to get the actual linearization.
				LinkedList<LinkedList<String>> toMerge = new LinkedList<>(baseLinearizations);
				LinkedList<String> linearization = merge(toMerge);
				if (linearization == null) {
					error("Linearization failed.");
				}
				contract.c3Linearization = linearization;
			}
		}

		/**
		 * See the function 'constructC3Linearization'.
		 * Performs the 'merge' step for the list of inheritance lists 'toMerge', as part of the C3 linearization.
		 * @param toMerge A list of inheritance lists for a contract, created from its inheritance tree.
		 * @return A C3 linearization for the contract corresponding to what is in 'toMerge'.
		 */
		private LinkedList<String> merge(final LinkedList<LinkedList<String>> toMerge) {
			LinkedList<String> linearization = new LinkedList<>();

			while (!toMerge.isEmpty()) {
				boolean candidateFound = false;
				String candidate = null;
				// Try to find a candidate by inspecting the head of all lists
				Iterator<LinkedList<String>> it = toMerge.iterator();
				while (it.hasNext()) {
					LinkedList<String> baseList = it.next();
					candidate = baseList.getLast();
					boolean appearsOnlyAtHead = true;
					// Check if the candidate appears only at the head of all lists, if it appears
					for (LinkedList<String> list2 : toMerge) {
						int candidatePos = list2.indexOf(candidate);
						if (candidatePos != -1 && candidatePos < list2.size() - 1) {
							appearsOnlyAtHead = false;
							break;
						}
					}
					if (appearsOnlyAtHead) {
						candidateFound = true;
						break;
					}
				}
				if (candidateFound) {
					// Add the candidate to the linearization, and remove it from all lists.
					linearization.addFirst(candidate);
					it = toMerge.iterator();
					while (it.hasNext()) {
						LinkedList<String> baseList = it.next();
						baseList.remove(candidate);
						if (baseList.isEmpty())
							it.remove();
					}
				} else {
					error("Cannot linearize; no suitable candidate found during the linearization step.");
				}
			}
			return linearization;
		}
	}

	/* The visitor is used to get the type of a Solidity expression. This is used so that proper function overloading
	   can occur when we encounter a function call, by examining the types of the arguments given.
	 */
	private class SolidityExpressionTypeVisitor extends SolidityBaseVisitor<String> {
		@Override
		public String visitAndExpression(SolidityParser.AndExpressionContext ctx) {
			return "boolean";
		}

		@Override
		public String visitArrayAccessExpression(SolidityParser.ArrayAccessExpressionContext ctx) {
			String arrId = ctx.expression(0).getText();
			return varStack.getTypeofIdentifier(arrId);
		}

		@Override
		public String visitAssignmentExpression(SolidityParser.AssignmentExpressionContext ctx) {
			return visit(ctx.expression(0));
		}

		@Override
		public String visitCompExpression(SolidityParser.CompExpressionContext ctx) {
			return "boolean";
		}

		@Override
		public String visitEqualityExpression(SolidityParser.EqualityExpressionContext ctx) {
			return "boolean";
		}

		@Override
		public String visitFunctionCallExpression(SolidityParser.FunctionCallExpressionContext ctx) {
			return convertType(resolveFunctionCall(ctx).callable.returnType);
		}

		@Override
		public String visitNotExpression(SolidityParser.NotExpressionContext ctx) {
			return "boolean";
		}

		@Override
		public String visitPrimaryExpression(SolidityParser.PrimaryExpressionContext ctx) {
			if (ctx.BooleanLiteral() != null) {
				return "boolean";
			} else if (ctx.numberLiteral() != null) {
				return "int";
			} else if (ctx.HexLiteral() != null) {
				return "int";
			} else if (ctx.StringLiteral() != null) {
				return "String";
			} else if (ctx.identifier() != null) {
				// TODO: could be "this"?
				return convertType(varStack.getTypeofIdentifier(ctx.getText()));
			} else if (ctx.tupleExpression() != null) {
				// TODO
				error("Tuple expressions not supported.");
				return "";
			} else if (ctx.elementaryTypeNameExpression() != null) {
				// TODO
				error("Elementary type name expressions not supported.");
				return "";
			} else {
				error("Unsupported primary expression encountered.");
				return "";
			}
		}

		@Override
		public String visitOrExpression(SolidityParser.OrExpressionContext ctx) {
			return "boolean";
		}

		@Override
		public String visitTernaryExpression(SolidityParser.TernaryExpressionContext ctx) {
			return visit(ctx.expression(1));
		}
	}
}