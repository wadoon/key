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
		FIELD_DECL_LEFT,
		FIELD_DECL_RIGHT,
		FUNCTION_BODY,
		FUNCTION_HEADER, // Note: does not include the list of modifier calls.
		MODIFIER_BODY,
		MODIFIER_HEADER,
		STRUCT
	}

	private enum FunctionCallReferenceType {
		INTERNAL, // ex: foo()
		CONTRACT, // ex: A.foo(), where A is a contract name
		INSTANCE, // ex: a.foo(), where a is a contract instance
		THIS,     // ex: this.foo()
		SUPER     // ex. super.foo()
	}

	private abstract class SolidityCallable {
		String name;
		String ownerName;
		String returnType;
		LinkedList<SolidityVariable> params = new LinkedList<>();

		@Override
		public String toString() {
			StringBuilder output = new StringBuilder();
			if (this instanceof SolidityFunction) {
				output.append(returnType);
				output.append(" ");
			}
			output.append(name);
			output.append('(');
			for (SolidityVariable param : params)
				output.append(param.toString());
			output.append(')');
			return output.toString();
		}

		public LinkedList<String> getParamTypeNames() {
			LinkedList<String> typeNames = new LinkedList<>();
			params.forEach(param -> typeNames.add(param.typename));
			return typeNames;
		}
	}

	private class SolidityFunction extends SolidityCallable {
		SolidityParser.FunctionDefinitionContext ctx;
		FunctionVisibility visibility;
		boolean isVirtual;
		boolean overrides;
		boolean isAbstract;
	}

	private class SolidityConstructor extends SolidityCallable {
		SolidityParser.ConstructorDefinitionContext ctx;
	}

	private class SolidityModifier extends SolidityCallable {
		SolidityParser.ModifierDefinitionContext ctx;
	}

	private class SolidityVariable {
		String name;
		String typename;
		boolean isConstant;

		SolidityVariable(String name, String typename) {
			this.name = name; this.typename = typename;
		}

		@Override
		public String toString() { return typename + " " + name; }
	}

	private class SolidityField extends SolidityVariable {
		String ownerName;
		FieldVisibility visibility;
		SolidityParser.StateVariableDeclarationContext ctx;

		SolidityField(String name, String typename) { super(name, typename); }
	}

	private class SolidityModifierVariable extends SolidityVariable {
		SolidityModifierVariable(String name, String typename) { super(name, typename); }
	}

	private class SolidityContract {
		String name;
		ContractType type;
		boolean isAbstract;
		LinkedList<String> inheritanceList = new LinkedList<>();
		LinkedList<String> c3Linearization = new LinkedList<>();
		LinkedList<SolidityFunction> functions = new LinkedList<>();
		LinkedList<SolidityField> fields = new LinkedList<>();
		LinkedList<SolidityModifier> modifiers = new LinkedList<>();
		SolidityConstructor constructor;

		SolidityFunction getFunction(String funName, List<String> argTypes) {
			for (SolidityFunction fun : functions) {
				if (fun.name.equals(funName) && fun.getParamTypeNames().equals(argTypes))
					return fun;
			}
			return null;
		}

		SolidityField getField(String fieldName) {
			for (SolidityField field : fields) {
				if (field.name.equals(fieldName))
					return field;
			}
			return null;
		}

		// Note: modifiers cannot be overloaded with different argument lists.
		SolidityModifier getModifier(String modName) {
			for (SolidityModifier mod : modifiers) {
				if (mod.name.equals(modName))
					return mod;
			}
			return null;
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

	private class CallableOverloadResult {
		String mangledName;
		SolidityCallable callable;
		CallableOverloadResult(String mangledName, SolidityCallable callable) {
			this.mangledName = mangledName; this.callable = callable;
		}
	}

	private class VariableScopeStack {
		private final Deque<LinkedList<SolidityVariable>> deque = new ArrayDeque<>();

		// Reset the stack to only include the fields of the current owner contract (and its inherit fields).
		public void resetToContractScope() {
			clear();
			for (String parentContractName : currentOwnerContract.c3Linearization) {
				SolidityContract parentContract = contracts.get(parentContractName);
				if (parentContract == null) {
					error("Could not locate contract " + parentContractName +
							" as a parent of contract" + currentContract.name);
				}
				newBlock(parentContract.fields);
			}
		}

		public void clear() {
			deque.clear();
		}

		public <T extends SolidityVariable> void pushVar(T var) {
			LinkedList<SolidityVariable> topContext = deque.peekFirst();
			if (topContext == null)
				error("Tried to declare a variable when outside of any scope.");
			topContext.add(var);

		}
		public void newBlock() {
			deque.addFirst(new LinkedList<>());
		}

		public void newBlock(LinkedList<? extends SolidityVariable> list) {
			deque.addFirst(new LinkedList<>(list));
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
			return var == null ? null : var.typename;
		}

		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder();
			for (LinkedList<SolidityVariable> scope : deque) {
				sb.append('[');
				for (SolidityVariable var : scope) {
					sb.append(var.toString());
					sb.append(", ");
				}
				sb.append("], ");
			}
			return sb.toString();
		}
	}

	private boolean nameIsAContract(String name) {
		return contracts.get(name) != null;
	}

	// https://docs.soliditylang.org/en/v0.8.12/units-and-global-variables.html
	// TODO: does not include ABI encoding/decoding functions
	private final List<String> reservedSolidityFunctions = Arrays.asList(
		"addmod", "assert", "blockhash", "call", "delegatecall", "ecrecover", "gasleft", "keccak256", "mulmod",
			"require", "revert", "ripemd160", "selfdestruct", "send", "sha256", "staticcall", "transfer"
	);

	private final VariableScopeStack varStack = new VariableScopeStack();
	private final Stack<ContractStructure> structureStack = new Stack<>();

    private Map<String,SolidityContract> contracts = new HashMap<>(); // Contract name => contract
	private SolidityContract currentContract; // The contract that we are currently visiting/building
	private SolidityContract currentOwnerContract; // If we are visiting e.g. an inherited function, then this will be the owner

	private StringBuilder interfaceBodyOutput = new StringBuilder();

	private String modifierUnderscoreReplacement; // What the statement '_;' is replaced with in a modifier body.

	public String output = "";

	/**
	 * Construct a mangled name for inherited functions/fields/modifiers. Fields are only mangled if they are private.
	 * @param baseContract The contract that the function/field/modifier was inherited from.
	 * @param identifier The function/field/modifier identifier.
	 * @return A mangled identifier.
	 */
	private String renameInheritedName(String baseContract, String identifier) {
		return "__" + baseContract + "__" + identifier;
	}

	private String renameModifierVariable(String identifier) {
		return "__mod__" + identifier;
	}

	private String renameContractTypeName(String contractName) {
		return contractName + "Impl";
	}

	/**
	 * Checks whether a function identifier is a reserved Solidity function name, e.g., 'require'.
	 * @param function The function identifier.
	 * @return True if the identifier is reserved, false otherwise.
	 */
	private boolean functionNameIsReserved(String function) {
		return reservedSolidityFunctions.contains(function);
	}

	/**
	 * Checks whether we are currently visiting a function/field/constructor/modifier that was inherited.
	 * @return The result of currentContract != currentOwnerContract.
	 */
	private boolean currentlyVisitingInheritedMember() {
		return currentContract != currentOwnerContract;
	}

	/**
	 * Constructs a Java interface for the contract that is currently being visited.
	 * This interface contains declarations for all functions that the contract introduces (not overrides), as well as
	 * enums and structs. The resulting Java class for the contract shall 'implement' this interface.
	 * The interface 'extends' all the corresponding interfaces for the contracts in the contract's inheritance list.
	 * @return The Java text output for the interface.
	 */
	private String makeInterface() {
		StringBuilder output = new StringBuilder();
		output.append("interface " + currentContract.name);

		// build 'extends' list
		if (currentContract.inheritanceList.size() > 0) {
			output.append(" extends");
			currentContract.inheritanceList.forEach(c -> output.append(" " + c + ","));
			output.deleteCharAt(output.length()-1);
		}
		output.append(" {\n");
		output.append(interfaceBodyOutput.toString());
		output.append("}\n");
		interfaceBodyOutput = new StringBuilder();
		return output.toString();
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

	private String renameInheritedFieldReferenceIfNecessary(SolidityField field) {
		// Rename the field if it is an inherited private field, but only if no other contract in the
		// inheritance hierarchy defines the field. This is to that a subcontract can "override" a name
		// that a supercontract already has defined, but privately.
		if (!field.ownerName.equals(currentContract.name) && field.visibility == FieldVisibility.PRIVATE) {
			boolean fieldFoundElsewhere = false;
			for (String parentName : currentContract.c3Linearization) {
				SolidityContract parent = contracts.get(parentName);
				if (parent.getField(field.name) != null && !parentName.equals(field.ownerName)) {
					fieldFoundElsewhere = true;
					break;
				}
			}
			if (fieldFoundElsewhere) {
				return "__" + field.ownerName + "__" + field.name;
			}
		}
		return field.name;
	}

	/**
	 * Resolve a function call; given the function call expression context and from where the function was called,
	 * perform overload resolution to determine which explicit function should be called.
	 * @param ctx The function call expression context.
	 * @return A tuple of 1) the (possibly mangled) name of the explicit function that is called,
	 * and 2) the function itself as a 'SolidityFunction', containing e.g. the context and signature.
	 */
	private CallableOverloadResult resolveFunctionCall(SolidityParser.FunctionCallExpressionContext ctx) {
		/* We have five different types of "function calls", one of them a constructor call, where overload resolution
		   is not actually done. During overload resolution, we walk up the linearization tree, starting from a
		   given contract, to find a suitable function. The below table lists whose linearization
		   list we use in which cases, and from where we start walking.
		   Note: s.super.foo() is not allowed.
		   Note: the below does not include calls to modifiers. Those go through 'visitFunctionDefinition' and
		   'visitConstructorDefinition' instead.
		   Below, 'C' is a contract name, and 'c' is a contract instance.
		Type					Example			Linearization owner		Linearization walk starting contract.
		internal				foo()			currentContract			currentContract
		external, direct: 		C.foo()			currentContract			C. foo must be in C
		external, instance: 	c.foo()			typeof(c)				typeof(c)
		this					this.foo()		================== Same as internal ==================
		super					super.foo()		currentContract			the contract before currentOwnerContract
		constructor				C()				does not apply			does not apply
		 */

		// TODO: we may not call an external function unless 'this' is used. Currently, this is not checked.

		String fctName = ctx.expression().getText();
		String contractName = fctName;
		String comparableName = fctName;

		FunctionCallReferenceType referenceType;
		boolean isConstructorCall = false;
		int dotPos = fctName.lastIndexOf('.');
		if (dotPos == -1) {
			referenceType = FunctionCallReferenceType.INTERNAL;
			// Currently, calls such as "new A()" gets turned into a function call to "newA"
			// TODO: possible fix this in the future.
			isConstructorCall = fctName.startsWith("new") && nameIsAContract(fctName.substring(3));
		} else {
			contractName = fctName.substring(0, dotPos);
			comparableName = fctName.substring(dotPos+1);
			if (contractName.equals("this")) {
				referenceType = FunctionCallReferenceType.THIS;
			} else if (contractName.equals("super")) {
				referenceType = FunctionCallReferenceType.SUPER;
			} else if (nameIsAContract(contractName)) {
				referenceType = FunctionCallReferenceType.CONTRACT;
			} else {
				referenceType = FunctionCallReferenceType.INSTANCE;
			}
		}

		// TODO: in the case of e.g. addr.transfer(), just return the entire function name. Is this fine?
		if (referenceType == FunctionCallReferenceType.INSTANCE && functionNameIsReserved(comparableName)) {
			return new CallableOverloadResult(fctName, null);
		}

		if (isConstructorCall) {
			// Since a contract can have at most one constructor, there is no need to resolve overloads.

			// Currently, calls such as "new A()" gets turned into a function call to "newA"
			// TODO: possible fix this in the future.
			SolidityContract ownerContract = contracts.get(fctName.substring(3));
			if (ownerContract == null)
				error("");
			String mangledName = "new " + renameContractTypeName(ownerContract.name);
			return new CallableOverloadResult(mangledName, ownerContract.constructor);
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

		SolidityContract caller; // Whose linearization to use. Essentially, the caller.
		String baseContract; // The walking of the linearization list should start from this contract.

		if (referenceType == FunctionCallReferenceType.INSTANCE) {
			String typeName = varStack.getTypeofIdentifier(contractName);
			caller = contracts.get(typeName);
		} else {
			caller = currentContract;
		}

		if (referenceType == FunctionCallReferenceType.SUPER) {
			baseContract = currentOwnerContract.name;
		} else if (referenceType == FunctionCallReferenceType.CONTRACT) {
			baseContract = contractName;
		} else {
			baseContract = caller.name;
		}

		/* When we walk up the linearization list, we must first find the contract 'baseContract',
		   which is from where the actual searching after the function starts.
		   'searchBaseContractForFunction' indicates whether we are allowed to search for the function
		   in 'baseContract', once we locate 'baseContract'.
		 */
		boolean baseContractFound = false;
		boolean searchBaseContractForFunction = referenceType != FunctionCallReferenceType.SUPER;

		SolidityFunction resolvedFun = null;
		Iterator<String> reverseIt = caller.c3Linearization.descendingIterator();
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

		String mangledName = referenceType == FunctionCallReferenceType.INSTANCE ? contractName + "." : "";
		if (resolvedFun.ownerName.equals(caller.name)) {
			mangledName += comparableName;
		} else {
			mangledName += renameInheritedName(resolvedFun.ownerName, comparableName);
		}

		return new CallableOverloadResult(mangledName, resolvedFun);
	}


	private CallableOverloadResult resolveModifierCall(SolidityParser.ModifierInvocationContext ctx) {
		String modName = ctx.identifier().getText();
		String comparableName = modName;
		String contractName = modName;
		int dotPos = modName.lastIndexOf('.');
		boolean isDirectCall = dotPos != -1;
		if (isDirectCall) {
			contractName = modName.substring(0, dotPos);
			comparableName = modName.substring(dotPos + 1);
		}

		if (isDirectCall) {
			SolidityContract parent = contracts.get(contractName);
			if (parent == null) {
				error("Contract " + currentOwnerContract.name + " calls modifier " + modName +
						", but contract " + contractName + " does not exist.");
			}
			if (currentOwnerContract.c3Linearization.contains(parent.name)) {
				error("Contract " + currentOwnerContract.name + " calls modifier " + modName +
						", but " + currentOwnerContract.name + " does not inherit from " + contractName);
			}
			for (SolidityModifier mod : parent.modifiers) {
				if (mod.name.equals(comparableName)) {
					String mangledName = mod.name;
					if (!contractName.equals(currentContract.name))
						mangledName = renameInheritedName(contractName, modName);
					return new CallableOverloadResult(mangledName, mod);
				}
			}
			error("Contract " + contractName + " does not contain the modifier " + modName);
		} else {
			Iterator<String> reverseIt = currentContract.c3Linearization.descendingIterator();
			while (reverseIt.hasNext()) {
				String parentName = reverseIt.next();
				SolidityContract parentContract = contracts.get(parentName);
				SolidityModifier mod = parentContract.getModifier(modName);
				if (mod != null) {
					String mangledName = String.valueOf(mod.name);
					if (!parentName.equals(currentContract.name))
						mangledName = renameInheritedName(parentName, modName);
					return new CallableOverloadResult(mangledName, mod);
				}
			}
			error("Could not resolve call to modifier " + modName);
		}
		return null;
	}

	/**
	 * "Flatten" a constructor or function by "baking in" its modifier and supercontract constructor invokations
	 * into the function body itself. This is done by creating an inner class in the function/constructor,
	 * and a function in this class is created for each modifier invokation. These functions are then called from
	 * inside the function in the order of the modifier list. Finally, the function itself is called
	 * (without modifiers). Constructor invocations simply become calls to external functions whose output have been
	 * created elsewhere. These calls are in the order of the current contract's C3 linearization, and are made
	 * before the modifiers are called.
	 * @param callable The constructor or function for which to perform the flattening for.
	 * @param callableBody The Java output of the constructor's/function's body.
	 * @param modCtxs A list of modifier invocations.
	 * @param constrCtxs A list of constructor invocations. It is assumed that these are sorted according to the
	 *                   current contract's C3 linearization.
	 * @return The Java output for the new function body.
	 */
	private String createFlattenedCallableBody(SolidityCallable callable, String callableBody,
											   List<SolidityParser.ModifierInvocationContext> modCtxs,
											   List<SolidityParser.ModifierInvocationContext> constrCtxs) {
		// Note: we are assuming that the constructor contexts are in the order of least to most derived.

		if (modCtxs == null || modCtxs.isEmpty()) {
			if (constrCtxs == null || constrCtxs.isEmpty()) {
				error("A call to createFlattenedCallableBody() was made, but the supplied modifier list is empty.");
			}
			// Add to the output the list of constructor calls that will be made if the callable is a constructor,
			// and the modifier list contains constructor calls. These are invoked before the modifiers are.
			// Note: we are assuming that the constructor contexts are in the order of least to most derived.
			StringBuilder output = new StringBuilder("{\n");
			for (SolidityParser.ModifierInvocationContext ctx : constrCtxs) {
				output.append(ctx.identifier().getText() + "Impl(msg,");
				if (ctx.expressionList() != null && !ctx.expressionList().expression().isEmpty()) {
					ctx.expressionList().expression().forEach(expr -> output.append(visit(expr) + ','));
				}
				output.deleteCharAt(output.length() - 1);
				output.append(");\n");
			}
			output.append(callableBody + "\n}");
			return output.toString();
		}

		List<SolidityModifier> mods = new LinkedList<>();
		HashMap<SolidityModifier, Integer> numberOfOccurrences = new HashMap<>();
		HashMap<SolidityModifier, Integer> numberOfTimesVisited = new HashMap<>();
		modCtxs.forEach(modCtx -> {
			CallableOverloadResult overloadResult = resolveModifierCall(modCtx);
			SolidityModifier mod = (SolidityModifier)(overloadResult.callable);
			mods.add(mod);
			numberOfOccurrences.merge(mod, 1, Integer::sum); // Add 1 to the count, or if null, make it 1.
			numberOfTimesVisited.putIfAbsent(mod, 0); // Start with 0 initially; below, we do the actual "visiting".
		});

		StringBuilder output = new StringBuilder("{\nclass __Modifiers {\n");

		// Create the function for the original function/constructor without any mods.
		// If we function returns something that is not void, we also create a field '__returnValue'.
		String returnType = null;
		String callableName = null;
		if (callable instanceof SolidityConstructor) {
			returnType = "void";
			callableName = "__no_mods__" + renameContractTypeName(callable.ownerName);
		} else if (callable instanceof SolidityFunction) {
			returnType = convertType(callable.returnType);
			callableName = "__no_mods__" + callable.name;
			if (!returnType.equals("void")) {
				output.append(returnType + " __returnValue = " + getDefaultValueOfType(returnType) + ";\n\n");
			}
		} else {
			error("Illegitimate SolidityCallable type given to createFlattenedCallableBody().");
		}
		output.append(returnType + " " + callableName + "(");
		callable.params.forEach(param -> output.append(param.toString() + ","));
		if (!callable.params.isEmpty())
			output.deleteCharAt(output.length() - 1);
		output.append(")" + callableBody + "\n\n");

		// For each modifier in the list, create a new function with the same name.
		// If a modifier occurs multiple times, we create one function per modifier occurrence, since,
		// whatever '_;' will be replaced with depends on where in the modifier list the modifier is called.
		// First, find what '_;' should actually be replaced with.
		int modIndex = -1;
		for (SolidityModifier mod : mods) {
			modIndex++;
			boolean isTheLastModifier = modIndex == mods.size() - 1;

			currentOwnerContract = contracts.get(mod.ownerName);
			varStack.resetToContractScope();

			structureStack.push(ContractStructure.MODIFIER_HEADER);

			// First, find what the underscore replacement should be. When the modifier block is visited and
			// an '_;' is encountered (see visitTerminal()), the replacement takes place.
			StringBuilder underscoreReplacement = new StringBuilder();

			if (isTheLastModifier) {
				if (callable instanceof SolidityFunction && !returnType.equals("void")) {
					underscoreReplacement.append("__returnValue = ");
				}
				underscoreReplacement.append(callableName + '(');
				callable.params.forEach(param -> underscoreReplacement.append(param.name + ","));
				if (!callable.params.isEmpty())
					underscoreReplacement.deleteCharAt(underscoreReplacement.length() - 1);
			} else {
				SolidityModifier nextMod = mods.get(modIndex + 1);
				SolidityParser.ModifierInvocationContext nextModCtx = modCtxs.get(modIndex + 1);
				underscoreReplacement.append(nextMod.name);
				if (numberOfOccurrences.get(nextMod) > 1)
					underscoreReplacement.append("__" + String.valueOf(numberOfTimesVisited.get(nextMod) + 1) + "__");
				underscoreReplacement.append('(');
				if (nextModCtx.expressionList() != null && !nextModCtx.expressionList().expression().isEmpty()) {
					for (SolidityParser.ExpressionContext exprCtx : nextModCtx.expressionList().expression()) {
						underscoreReplacement.append(visit(exprCtx) + ",");
					}
					underscoreReplacement.deleteCharAt(underscoreReplacement.length() - 1);
				}
			}
			underscoreReplacement.append(");");

			modifierUnderscoreReplacement = underscoreReplacement.toString();
			underscoreReplacement.delete(0, underscoreReplacement.length());

			// Second, add to the output the function for the modifier.

			output.append("void ");
			if (currentlyVisitingInheritedMember()) {
				output.append(renameInheritedName(currentOwnerContract.name, mod.name));
			} else {
				output.append(mod.name);
			}
			if (numberOfOccurrences.get(mod) > 1) {
				output.append("__" + numberOfTimesVisited.get(mod) + "__");
			}
			output.append('(');

			mod.params.forEach(param ->
				output.append(param.typename + " " + renameModifierVariable(param.name) + ",")
			);
			if (output.charAt(output.length() - 1) == ',') {
				output.deleteCharAt(output.length() - 1);
			}
			output.append(")\n");
			structureStack.pop();
			structureStack.add(ContractStructure.MODIFIER_BODY);
			varStack.newBlock(mod.params);
			output.append(visit(mod.ctx.block()));
			varStack.exitBlock();
			structureStack.pop();
			output.append("\n\n");

			Integer numTimesVisited = numberOfTimesVisited.get(mod);
			numberOfTimesVisited.put(mod, numTimesVisited + 1);
		}
		output.append("}\n\n");



		// Add to the output the list of constructor calls that will be made if the callable is a constructor,
		// and the modifier list contains constructor calls. These are invoked before the modifiers are.
		if (constrCtxs != null && !constrCtxs.isEmpty()) {
			// Note: we are assuming that the constructor contexts are in the order of least to most derived.
			for (SolidityParser.ModifierInvocationContext ctx : constrCtxs) {
				output.append(ctx.identifier().getText() + "Impl(msg,");
				if (ctx.expressionList() != null && !ctx.expressionList().expression().isEmpty()) {
					ctx.expressionList().expression().forEach(expr -> output.append(visit(expr) + ','));
				}
				output.deleteCharAt(output.length() - 1);
				output.append(");\n");
			}
		}

		// Create an instance of the Modifier class, if there is at least one modifier.
		// If so, call the first modifier, and return the return value.
		SolidityModifier firstMod = mods.get(0);
		SolidityParser.ModifierInvocationContext firstModCtx = modCtxs.get(0);
		output.append("__Modifiers mods = new __Modifiers();\n");
		String mangledName = String.valueOf(firstMod.name);
		if (currentlyVisitingInheritedMember()) {
			mangledName = renameInheritedName(currentOwnerContract.name, mangledName);
		}
		output.append("mods." + mangledName);
		if (numberOfOccurrences.get(firstMod) > 1)
			output.append("__0__");
		output.append('(');
		if (firstModCtx.expressionList() != null && !firstModCtx.expressionList().expression().isEmpty()) {
			firstModCtx.expressionList().expression().forEach(expr -> output.append(visit(expr) + ","));
		}
		if (output.charAt(output.length() - 1) == ',')
			output.deleteCharAt(output.length() - 1);
		output.append(");\n");
		if (!returnType.equals("void")) {
			output.append("return mods.__returnValue;\n");
		}
		output.append('}');

		return output.toString();
	}

	private String getDefaultValueOfType(String typeName) {
		return switch (convertType(typeName)) {
			case "int" -> "0";
			case "boolean" -> "false";
			default -> "null";
		};
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

		varStack.resetToContractScope();

		// Create a class/interface from the contract and visit each of its children
        final StringBuffer contractOutput = new StringBuffer();
        if (contract.type == ContractType.CONTRACT) {
			if (contract.isAbstract)
				contractOutput.append("abstract ");
			contractOutput.append("class " + contractName + "Impl extends Address implements " + contractName + " {\n");
        } else if (contract.type == ContractType.INTERFACE) {
			contractOutput.append("interface " + contractName);
            if (contract.inheritanceList.size() > 0) {
				contractOutput.append(" extends");
				contract.inheritanceList.forEach(c -> contractOutput.append(" " + c + ","));
				contractOutput.setCharAt(contractOutput.length()-1,' ');
            }
			contractOutput.append(" {\n");
        } else if (contract.type == ContractType.LIBRARY) {
			contractOutput.append("class " + contractName + " {\n");
        } else {
			error("Unrecognized contract type for contract " + contractName + " encountered.");
		}
		ctx.contractPart().stream().forEach(part -> contractOutput.append(visit(part) + '\n'));

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
			varStack.resetToContractScope();

			// Note: modifiers are only imported once they are invoked in a function/constructor definition.

			// Import fields (textually)
			if (parent.fields == null)
				error("Could not locate parent contract " + parentName + " to " +
						currentContract.name + " when importing inherited fields.");
			parent.fields.forEach(field -> contractOutput.append(visit(field.ctx) + '\n'));

			// Import functions.
			// Note: these may also visit modifiers imported from other constructors,
			// so we need to reassign 'currentOwnerContract' every time, for this gets reassigned to the modifier owner.
			// Also, the variable stack may change to only contain the fields of the owner, so we reset this too.
			if (parent.functions == null)
				error("Could not locate parent contract " + parentName + " to " +
						currentContract.name + " when importing inherited functions.");
			parent.functions.forEach(fun -> {
				contractOutput.append(visit(fun.ctx) + '\n');
				currentOwnerContract = parent;
				varStack.resetToContractScope();
			});

			// Import constructors (as functions). Each base class can have at most one constructor.
			// As with functions, the constructor may also visit modifiers imported from other contracts.
			if (parent.hasNonDefaultConstructor())
				contractOutput.append(visit(parent.constructor.ctx) + '\n');
			currentOwnerContract = parent;
			varStack.resetToContractScope();
		}

		/* For contracts, an interface is created in addition to the flattened contract, so that type information
		   from the inheritance hierarchy is kept. The interface shall contain function declarations and
		   enum and struct definitions.
		   If the "contract" is an interface, include these things here already.
		 */
		if (contract.type == ContractType.CONTRACT) {
			output += makeInterface();
		}
		interfaceBodyOutput = new StringBuilder(); // reset the interface output for the next contract.

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
		structureStack.push(ContractStructure.FIELD_DECL_LEFT);

		SolidityField field = currentOwnerContract.getField(ctx.identifier().getText());

		String output = "  ";

		switch (field.visibility) {
			case PUBLIC -> output += "public";
			case PRIVATE -> output += "private";
			// The default visibility is "internal", roughly corresponding to java's "protected".
			default -> output += "protected";
		}
		if (field.isConstant) {
			output += "final";
		}

		String renamedIdentifier = renameInheritedFieldReferenceIfNecessary(field);

		String shownTypename = String.valueOf(field.typename);
		if (nameIsAContract(field.typename))
			shownTypename = renameContractTypeName(shownTypename);

		output += " " + shownTypename + " " + renamedIdentifier;

		structureStack.pop();
		structureStack.push(ContractStructure.FIELD_DECL_RIGHT);

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
		StringBuffer output = new StringBuffer("static class " + visit(ctx.identifier()) + "{\n");
		ctx.variableDeclaration().stream().forEach(v -> output.append(visit(v)).append(";\n"));
		output.append("}\n");
		interfaceBodyOutput.append(output);
		structureStack.pop();
		return ""; // Structs are added only to the interface output, just like enums are.
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitConstructorDefinition(SolidityParser.ConstructorDefinitionContext ctx) {
		structureStack.push(ContractStructure.CONSTRUCTOR_HEADER);

		SolidityConstructor constructor = currentOwnerContract.constructor;

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

		StringBuilder output = new StringBuilder(
				visibility + " " + currentOwnerContract.name + "Impl(" + parameters + ")");

		structureStack.pop();

		if (ctx.block() == null) {
			error("Constructor must be defined if declared. See contract " + currentContract.name + ".");
		}

		structureStack.push(ContractStructure.CONSTRUCTOR_BODY);
		varStack.newBlock(constructor.params);
		String bodyOutput = visit(ctx.block());
		varStack.exitBlock();
		structureStack.pop();

		if (!ctx.modifierList().modifierInvocation().isEmpty()) {
			structureStack.push(ContractStructure.CONSTRUCTOR_HEADER);

			// A constructor "modifier" may be a call to a parent constructor, or to an actual modifier. Collect those.
			LinkedList<SolidityParser.ModifierInvocationContext> constructorCalls = new LinkedList<>();
			LinkedList<SolidityParser.ModifierInvocationContext> modCalls = new LinkedList<>();
			for (SolidityParser.ModifierInvocationContext mod : ctx.modifierList().modifierInvocation()) {
				String identifier = visit(mod.identifier());

				// Check whether the identifier is a modifier or a constructor
				int linearizationPos = currentOwnerContract.c3Linearization.indexOf(identifier);
				boolean isConstructorInvocation = linearizationPos != -1;
				if (!isConstructorInvocation) {
					modCalls.add(mod);
				} else {
					// The constructors should be in the order of the contract's linearization list.
					int insertPos = 0;
					for (SolidityParser.ModifierInvocationContext constrCall : constructorCalls) {
						int existingPos = currentContract.c3Linearization.indexOf(constrCall.identifier().getText());
						if (linearizationPos < existingPos)
							break;
						insertPos++;
					}
					constructorCalls.add(insertPos, mod);
				}
			}
			structureStack.pop();

			bodyOutput = createFlattenedCallableBody(constructor, bodyOutput, modCalls, constructorCalls);
		}
		output.append(bodyOutput);

		return output.toString();
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitModifierDefinition(SolidityParser.ModifierDefinitionContext ctx) {
		return ""; // Modifiers are not visited until they are invoked in a constructor/function definition.
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitModifierInvocation(SolidityParser.ModifierInvocationContext ctx) {
		return ""; // Modifiers are not visited until they are invoked in a constructor/function definition.
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitFunctionDefinition(SolidityParser.FunctionDefinitionContext ctx) {
		structureStack.push(ContractStructure.FUNCTION_HEADER);

		String funName = ctx.identifier().getText();
		LinkedList<String> argTypes = new LinkedList<>();
		ctx.parameterList().parameter().forEach(parameter -> argTypes.add(visit(parameter.typeName())));
		SolidityFunction function = currentOwnerContract.getFunction(funName, argTypes);

		String visibility = "";
		switch (function.visibility) {
			case PUBLIC, EXTERNAL -> visibility = "public";
			case INTERNAL -> visibility = "protected";
			case PRIVATE -> visibility = "private";
			default -> {
			}
		}

		String mangledName = String.valueOf(function.name);
		if (currentlyVisitingInheritedMember()) {
			mangledName = renameInheritedName(currentOwnerContract.name, mangledName);
		}

		StringBuilder parameters = new StringBuilder("Message msg,");
		ctx.parameterList().parameter().stream().forEach(param -> 
			parameters.append(visit(param) + ","));
		parameters.deleteCharAt(parameters.length() - 1);

		String returnType = convertType(function.returnType);

		String fctHeader = visibility + (currentContract.type == ContractType.LIBRARY ? " static " : " ") +
				(function.isAbstract ? "abstract " : "") +
				returnType + " " + mangledName + "(" + parameters + ")";

		/* If visiting a contract, the function declaration is added to an interface accompanying the
		   output class, unless the function was inherited.
		   If visiting a Solidity interface, the function body is empty, and the declaration is added right away
		   (see below).
		   If visiting a contract, with the function being abstract, it is added to the class as an abstract method,
		   and only added to the interface if its visibility is either public or package-protected.
		   This is because Java interface cannot have private/protected methods.
		 */
		if (currentContract.type == ContractType.CONTRACT &&
				!currentlyVisitingInheritedMember() && !function.overrides &&
				(visibility.equals("public")) || visibility.equals("")) {
			interfaceBodyOutput.append(fctHeader + ";\n");
		}

		structureStack.pop();

		String bodyOutput;
		if (function.isAbstract) {
			bodyOutput = ";";
		} else {
			structureStack.push(ContractStructure.FUNCTION_BODY);
			varStack.newBlock(function.params);
			bodyOutput = visit(ctx.block());
			varStack.exitBlock();
			structureStack.pop();
			if (!ctx.modifierList().modifierInvocation().isEmpty()) {
				bodyOutput = createFlattenedCallableBody(
						function, bodyOutput, ctx.modifierList().modifierInvocation(), null);
			}
		}

		return fctHeader + " " + bodyOutput;
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
		interfaceBodyOutput.append(enumDef.toString() + '\n');
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
		// Do not visit the identifier; if the name already exists and is an inherited private field,
		// we do not want to rename it, as visitIdentifier() would do.
		// We also don't want visitIdentifier() to rename it if we are in a modifier, and we are shadowing a modifier var.
		String identifier = ctx.identifier().getText();
		String typename = visit(ctx.typeName());

		String shownTypename = typename;
		if (nameIsAContract(typename)) // If it is a contract type
			shownTypename = renameContractTypeName(shownTypename);

		SolidityVariable var;
		if (structureStack.contains(ContractStructure.MODIFIER_BODY)) { // We are inside a modifier
			// Prepend '__mod__' to the name of the new variable, where 'mod' is modifier's name.
			var = new SolidityModifierVariable(identifier, typename);
			varStack.pushVar(var);
			String mangledIdentifier = String.valueOf(identifier);
			mangledIdentifier = renameModifierVariable(mangledIdentifier);
			return shownTypename + " " + mangledIdentifier;
		} else {
			var = new SolidityVariable(identifier, typename);
			varStack.pushVar(var);
			return shownTypename + " " + identifier;
		}
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
		return "while ( " + condition + " ) " + body;
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
		StringBuilder result = new StringBuilder("for (");
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
		return "return" + (ctx.expression() == null ? ";" : " " + visit(ctx.expression())+";");
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
		structureStack.push(ContractStructure.FIELD_DECL_LEFT);
		String decl = this.visit(ctx.variableDeclaration());
		structureStack.pop();

		if (ctx.variableDeclaration() != null) { // If it is a declaration of one variable...
			if (ctx.expression() != null){
				structureStack.push(ContractStructure.FIELD_DECL_RIGHT);
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
			CallableOverloadResult overload = resolveFunctionCall(ctx);
			mangledName = overload.mangledName;
		}

		StringBuffer arguments;
        boolean skip = false;
		switch (mangledName) {
			case "require2" -> {
				arguments = new StringBuffer("(int)sender != 0,");
				mangledName = "require";
				skip = true;
			}
			case "require3" -> {
				arguments = new StringBuffer("(int)recipient != 0,");
				mangledName = "require";
				skip = true;
			}
			case "require", "assert", "push" -> arguments = new StringBuffer();
			default -> arguments = new StringBuffer("msg,");
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
		return  visitChildren(ctx);
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
		else if (ctx.numberLiteral() != null)
			return ctx.numberLiteral().getText();
		else if (ctx.HexLiteral() != null)
			return ctx.HexLiteral().getText();
		else if (ctx.StringLiteral() != null)
			return ctx.StringLiteral().getText();
		else if (ctx.tupleExpression() != null)
			error("Tuple expressions are not yet supported.");
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

		SolidityVariable var = varStack.getVariableFromIdentifier(identifier);
		if (var == null) {
			return identifier;
		}
		// If the variable has been declared inside a modifier, we rename it
		if (var instanceof SolidityModifierVariable) {
			return renameModifierVariable(identifier);
		}
		/* If the identifier is of a private field that has been inherited, then this should be mangled.
		   This is because a subcontract may define a field with the same identifier.
		   However, the flattened contract shall contain both of these fields.
		   The name should not be mangled if resides in a definition where a new name is introduces, e.g.,
		   the header of a function/modifier/constructor definition, or on the left side of the '=' in a
		   variable declaration.
		 */
		if (var instanceof SolidityField && currentlyVisitingInheritedMember()) {
			return switch (structureStack.peek()) {
				case CALLABLE_INVOCATION, CONSTRUCTOR_BODY, FUNCTION_BODY, MODIFIER_BODY, FIELD_DECL_RIGHT ->
						renameInheritedFieldReferenceIfNecessary((SolidityField) var);
				default -> identifier;
			};
		}
		return identifier;
	}

	@Override public String visitTerminal(TerminalNode n) {
		// We are now visiting the _; statement found inside of modifiers.
		return modifierUnderscoreReplacement;
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
		SolidityCallable currentCallable;

		@Override
		public HashMap<String, SolidityContract> visitSourceUnit(SolidityParser.SourceUnitContext ctx) {
			ctx.contractDefinition().forEach(contract -> visit(contract));
			return contracts;
		}

		@Override
		public HashMap<String, SolidityContract> visitContractDefinition(SolidityParser.ContractDefinitionContext ctx) {
			String contractName = ctx.identifier().getText();
			if (nameIsAContract(contractName)) {
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
				constructor.name = constructor.ownerName = constructor.returnType = contract.name;
				constructor.params = new LinkedList<>();
			}

			// If any function was abstract, mark the class as abstract
			boolean hasAbstractFunction = false;
			for (SolidityFunction fun : contract.functions) {
				if (fun.isAbstract) {
					hasAbstractFunction = true;
					break;
				}
			}
			contract.isAbstract = hasAbstractFunction;

			return contracts;
		}

		@Override
		public HashMap<String, SolidityContract> visitFunctionDefinition(SolidityParser.FunctionDefinitionContext ctx) {
			SolidityFunction function = new SolidityFunction();
			currentContract.functions.add(function);
			currentCallable = function;
			String fctName = ctx.identifier() == null ? "fallback" : ctx.identifier().getText();
			function.ctx = ctx;
			function.name = fctName;
			function.ownerName = currentContract.name;

			function.returnType = ctx.getParent() instanceof ConstructorDefinitionContext ? "" : "void";
			if (ctx.returnParameters() != null && !ctx.returnParameters().isEmpty()) {
				function.returnType = ctx.returnParameters().parameterList().parameter(0).typeName().getText();
			}

			function.isAbstract = ctx.block() == null;
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
			currentCallable = modifier;
			modifier.name = ctx.identifier() == null ? "fallback" : ctx.identifier().getText();
			modifier.ctx = ctx;
			modifier.ownerName = currentContract.name;
			// Check for null here because modifiers can be declared like this: 'modifier mod { _; }', without the '()'
			if (ctx.parameterList() != null && !ctx.parameterList().parameter().isEmpty()) {
				ctx.parameterList().parameter().forEach(param -> visit(param));
			}
			// Note: modifiers' visibility cannot be specified (they are always private).
			return contracts;
		}

		@Override
		public HashMap<String, SolidityContract> visitStateVariableDeclaration(SolidityParser.StateVariableDeclarationContext ctx) {
			SolidityField field = new SolidityField(ctx.identifier().getText(), convertType(ctx.typeName().getText()));
			field.ctx = ctx;
			field.ownerName = currentContract.name;
			currentContract.fields.add(field);

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
			constructor.name = constructor.ownerName = constructor.returnType = currentContract.name;
			// As of now, there is no need to determine the arg types for the constructor. No constructor overloading
			// is done, since a contract only can contain at most one constructor.
			return contracts;
		}

		@Override
		public HashMap<String, SolidityContract> visitParameter(SolidityParser.ParameterContext ctx) {
			String name = ctx.identifier().getText();
			String typeName = convertType(ctx.typeName().getText());
			SolidityVariable var;
			if (currentCallable instanceof SolidityModifier) {
				var = new SolidityModifierVariable(name, typeName);
			} else {
				var = new SolidityVariable(name, typeName);
			}
			currentCallable.params.add(var);
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
				contract.c3Linearization = new LinkedList<>(Collections.singleton(contract.name));
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
				contract.c3Linearization = merge(toMerge);
			}
		}

		/**
		 * Check whether 'candidate' appears only at the end of all lists, if it appears at all.
		 * @param candidate
		 * @param lists
		 * @return
		 */
		private boolean appearsOnlyAtEnd(final String candidate, final LinkedList<LinkedList<String>> lists) {
			for (LinkedList<String> list : lists) {
				int candidatePos = list.indexOf(candidate);
				if (candidatePos != -1 && candidatePos < list.size() - 1) {
					return false;
				}
			}
			return true;
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
				for (LinkedList<String> baseList : toMerge) {
					candidate = baseList.getLast();
					// Check whether the candidate appears only at the head of all lists, if it appears at all
					if (appearsOnlyAtEnd(candidate, toMerge)) {
						candidateFound = true;
						break;
					}
				}
				if (candidateFound) {
					// Add the candidate to the linearization, and remove it from all lists.
					linearization.addFirst(candidate);
					Iterator<LinkedList<String>> it = toMerge.iterator();
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
				String typeName = varStack.getTypeofIdentifier(ctx.getText());
				if (typeName == null)
					error("Could not find the type of identifier " + ctx.identifier().getText() +
							" in contract " + currentContract.name);
				return convertType(typeName);
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