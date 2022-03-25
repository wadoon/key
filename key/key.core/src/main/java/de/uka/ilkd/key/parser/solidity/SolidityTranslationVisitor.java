package de.uka.ilkd.key.parser.solidity;

import org.antlr.v4.runtime.tree.TerminalNode;

import de.uka.ilkd.key.parser.solidity.SolidityParser.ConstructorDefinitionContext;
import de.uka.ilkd.key.parser.solidity.SolidityParser.InheritanceSpecifierContext;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class SolidityTranslationVisitor extends SolidityBaseVisitor<String> {
	public StringBuilder output = new StringBuilder();

	private final String defaultReturnVariableName = "__returnVal";
	private final VariableScopeStack varStack = new VariableScopeStack();
	private final Stack<ContractStructure> structureStack = new Stack<>();
	private Map<String,SolidityContract> contracts = new HashMap<>(); // Contract name => contract
	private SolidityContract currentContract; // The contract that we are currently visiting/building
	private SolidityContract currentOwnerContract; // If we are visiting e.g. an inherited function, then this will be the owner
	private StringBuilder interfaceOutput = new StringBuilder();
	private String modifierUnderscoreReplacement; // What the statement '_;' is replaced with in a modifier body.
	private String modifierReturnStmntReplacement; // What "return;" is replaced with in a modifier body.

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
		CALLABLE_HEADER, // Note: does not include the potential list of modifier/parent-constructor calls.
		CONSTRUCTOR_BODY,
		CONTRACT_DEF,
		ENUM,
		FIELD_DECL_LEFT,
		FIELD_DECL_RIGHT,
		FUNCTION_BODY,
		MODIFIER_BODY,
		MODIFIER_INVOCATION_FLATTENING, // A call is being made to a modifier during modifier flattening.
		STRUCT
	}

	private enum FunctionCallReferenceType {
		INTERNAL, // ex: foo()
		CONTRACT, // ex: A.foo(), where 'A' is a contract name
		LIBRARY,  // ex: L.foo(), where 'L' is a library name
		OBJECT, // ex: a.foo(), where 'a' is an instance of a contract, struct, or elementary type
		THIS,     // ex: this.foo()
		SUPER     // ex. super.foo()
	}

	private enum ModifierFlatteningMode {
		// Each modifier body, and the function/constructor body itself, is inlined into a single method.
		INLINE_MODS_INLINE_FUNCTION,

		// Each modifier body is inlined, but the function/constructor gets its own method and invoked from the main
		// method/constructor. This produces two callables in total.
		INLINE_MODS_CALL_FUNCTION,

		// Each modifier body, as well as the function/constructor, gets its own method. Each modifier calls the
		// next modifier in the invocation list every time an '_;' statement is encountered.
		CALL_MODS_CALL_FUNCTION
	}

	// TODO: model abi, global vars 'block' and 'tx'.

	// https://docs.soliditylang.org/en/v0.8.12/units-and-global-variables.html
	private final Map<String, String> reservedFreeFunctions = new HashMap<>() {
		{ // function name => return type
			put("addmod", "uint");
			put("assert", "void");
			put("blockhash", "bytes32");
			put("ecrecover", "address");
			put("gasleft", "(uint256)");
			put("keccak256", "bytes32");
			put("mulmod", "uint");
			put("require", "void");
			put("revert", "void");
			put("ripemd160", "bytes20");
			put("selfdestruct", "void");
			put("sha256", "bytes32");
		}
	};

	private final Map<String, String> reservedAddressFunctions = new HashMap<>() {
		{
			put("call", "(bool, bytes)");
			put("delegatecall", "(bool, bytes)");
			put("send", "bool");
			put("staticcall", "(bool, bytes)");
			put("transfer", "void");
		}
	};

	private final Map<String, String> reservedAddressFields = new HashMap<>() {
		{
			put("balance", "uint256");
			put("code", "bytes");
			put("codehash", "bytes32");
		}
	};

	private final Map<String, String> reservedMsgFields = new HashMap<>() {
		{
			put("data", "bytes");
			put("sender", "address");
			put("sig", "bytes4");
			put("value", "uint");
		}
	};

	private final Map<String, String> reservedBytesFunctions = new HashMap<>() {
		{
			put("concat", "bytes");
		}
	};

	private final Map<String, String> reservedStringFunctions = new HashMap<>() {
		{
			put("concat", "string");
		}
	};

	private final Map<String, String> reservedArrayFields = new HashMap<>() {
		{
			put("length", "uint");
		}
	};

	private final Map<String, String> reservedArrayFunctions = new HashMap<>() {
		{
			put("pop", "void");
			put("push", "void");
		}
	};

	private abstract class SolidityCallable {
		String name;
		String ownerName;
		String returnType; // Solidity type
		LinkedList<SolidityVariable> params = new LinkedList<>();

		@Override public String toString() {
			return name + this.buildParamListWithParen();
		}

		public LinkedList<String> getParamTypeNames() {
			LinkedList<String> typeNames = new LinkedList<>();
			params.forEach(param -> typeNames.add(param.typename));
			return typeNames;
		}

		public String buildParamList() {
			StringBuilder output = new StringBuilder("Message msg,");
			params.forEach(param -> output.append(param.toString() + ','));
			output.deleteCharAt(output.length() - 1);
			return output.toString();
		}

		public String buildParamListWithParen() {
			return "(" + buildParamList() + ")";
		}

		public String buildArgList() {
			StringBuilder output = new StringBuilder("msg,");
			params.forEach(param -> output.append(param.name + ','));
			output.deleteCharAt(output.length() - 1);
			return output.toString();
		}

		public String buildArgListWithParen() {
			return "(" + buildArgList() + ")";
		}

		/**
		 * Get the name of the callable as it would be displayed from the POV of 'callingContract'
		 * (either as a definition or call). I.e., if the callable has been imported from another contract,
		 * the display name may contain as a prefix the name of the contract that originally implemented the callable.
		 * @param callingContract The contract in which the callable should 'displayed' (called or defined).
		 * @return The display name.
		 */
		public abstract String getDisplayName(SolidityContract callingContract);

		/**
		 * Get the name of the callable as it would be displayed from the POV of 'callingContract', if the callable
		 * has undergone modifier flattening, and this is the version of the callable free of modifiers.
		 * @param callingContract The contract in which the callable should 'displayed' (called or defined).
		 * @return The modifier-free display name.
		 */
		public abstract String getModFreeDisplayName(SolidityContract callingContract);

		/**
		 * Checks if there exists an override of this callable anywhere in the inheritance tree of 'callingContract'.
		 * @param callingContract The contract whose C3 linearization will be checked for overrides.
		 * @return True if there exists an override, otherwise false.
		 */
		public abstract boolean hasOverride(SolidityContract callingContract);

		public abstract String visitBody();
		public abstract boolean hasReturnStatement();
	}

	private class SolidityFunction extends SolidityCallable {
		SolidityParser.FunctionDefinitionContext ctx;
		FunctionVisibility visibility;
		boolean isVirtual;
		boolean overrides;
		boolean isAbstract;
		boolean isPayable;
		boolean isPure;
		boolean isView;
		boolean isLibraryFunction;
		List<SolidityVariable> returnVars = new LinkedList<>();

		@Override
		public String toString() {
			return solidityToJavaType(returnType) + " " + name + this.buildParamListWithParen();
		}

		@Override
		public String getDisplayName(SolidityContract callingContract) {
			if (!this.ownerName.equals(callingContract.name) && this.hasOverride(callingContract)) {
				return "__" + ownerName + "__" + name;
			} else {
				return name;
			}
		}

		@Override
		public String getModFreeDisplayName(SolidityContract callingContract) {
			String normalDisplayName = getDisplayName(callingContract);
			if (normalDisplayName.startsWith("__")) {
				return "__unmod" + normalDisplayName;
			} else {
				return "__unmod__" + normalDisplayName;
			}
		}

		@Override
		public String visitBody() {
			varStack.newBlock(params);
			structureStack.push(ContractStructure.FUNCTION_BODY);
			String output = visit(ctx.block());
			structureStack.pop();
			varStack.exitBlock();
			return output;
		}

		@Override
		public boolean hasReturnStatement() { return blockHasReturnStatement(ctx.block()); }

		@Override
		public boolean hasOverride(SolidityContract callingContract) {
			boolean functionFound = false;
			for (String parentName : callingContract.c3Linearization) {
				SolidityContract parent = contracts.get(parentName);
				for (SolidityFunction parentFunction : parent.functions) {
					if (!parentFunction.isAbstract && parentFunction.name.equals(this.name) &&
							parameterListsAreEqual(parentFunction.getParamTypeNames(), this.getParamTypeNames())) {
						if (functionFound) {
							return true;
						} else {
							functionFound = true;
							break;
						}
					}
				}
			}
			return false;
		}

		public String declareFunctionReturnVars() {
			if (returnType.equals("void")) {
				return "";
			}
			else if (returnVars.isEmpty()) {
				return solidityToJavaType(returnType) + " " + defaultReturnVariableName +
						" = " + defaultValueOfType(returnType) + ";\n";
			} else {
				StringBuilder output = new StringBuilder();
				returnVars.forEach(var -> output.append(
						solidityToJavaType(var.typename) + " " + var.name + " = " + defaultValueOfType(var.typename) + ";\n"));
				return output.toString();
			}
		}

		public String makeFunctionReturnStmnt() {
			if (returnType.equals("void")) {
				return "";
			} else {
				if (returnVars.isEmpty()) {
					return "return " + defaultReturnVariableName + ";\n";
				} else {
					// TODO: for now, we return only the first return variable. In the future, return tuples of some kind.
					return "return " + returnVars.get(0).name + ";\n";
				}
			}
		}

		public String makeReturnVarAssignment() {
			if (returnType.equals("void")) {
				error("Cannot assign to return variables when the function returns void.");
				return "";
			} else {
				if (returnVars.isEmpty()) {
					return defaultReturnVariableName + " = ";
				} else {
					// TODO: for now, we assign only to the first return variable. In the future, return tuples of some kind.
					return returnVars.get(0).name + " = ";
				}
			}
		}
	}

	private class SolidityConstructor extends SolidityCallable {
		SolidityParser.ConstructorDefinitionContext ctx;

		@Override
		public String getDisplayName(SolidityContract callingContract) { return ownerName + "Impl"; }

		@Override
		public String getModFreeDisplayName(SolidityContract callingContract) {
			return "__unmod__" + getDisplayName(callingContract);
		}

		@Override
		public boolean hasOverride(SolidityContract callingContract) {
			return false; // Constructors cannot be overridden
		}

		@Override
		public boolean hasReturnStatement() { return blockHasReturnStatement(ctx.block()); }

		@Override
		public String visitBody() {
			varStack.newBlock(params);
			structureStack.push(ContractStructure.CONSTRUCTOR_BODY);
			String output = visit(ctx.block());
			structureStack.pop();
			varStack.exitBlock();
			return output;
		}

		/**
		 * Get a list of parent constructors that the constructor *explicitly* invokes.
		 * @return A list of parent constructors that the constructor invokes, in the invocation order.
		 */
		public List<SolidityParser.ModifierInvocationContext> getAllParentConstructorInvocations() {
			if (this.isDefaultConstructor()) {
				return new LinkedList<>();
			}
			List<SolidityParser.ModifierInvocationContext> invCtxs = new LinkedList<>();
			if (ctx.modifierList() != null) {
				for (SolidityParser.ModifierInvocationContext invCtx : ctx.modifierList().modifierInvocation()) {
					if (contracts.get(this.ownerName).c3Linearization.contains(invCtx.identifier().getText())) {
						invCtxs.add(invCtx);
					}
				}
			}
			return invCtxs;
		}

		public boolean isDefaultConstructor() { return this.ctx == null; }
	}

	private class SolidityModifier extends SolidityCallable {
		SolidityParser.ModifierDefinitionContext ctx;

		@Override
		public String getDisplayName(SolidityContract callingContract) {
			if (!this.ownerName.equals(callingContract.name) && this.hasOverride(callingContract)) {
				return "__" + ownerName + "__" + name;
			} else {
				return name;
			}
		}

		@Override
		public String getModFreeDisplayName(SolidityContract callingContract) {
			error("Cannot get the modifier-free name of a modifier.");
			return null; // a modifier-free modifier does not exist.
		}

		private String getDisplayName(SolidityContract callingContract, SolidityCallable mainCallable,
									  int invocationIndex, int totalInvocations)
		{
			StringBuilder output = new StringBuilder();
			String shownCallableName = mainCallable.getDisplayName(callingContract);
			String shownModName = this.getDisplayName(callingContract);
			if (shownCallableName.startsWith("__"))
				output.append("_");
			else
				output.append("___");
			output.append(shownCallableName + "___");
			if (shownModName.startsWith("__"))
				output.append(shownModName.substring(2));
			else
				output.append(shownModName);
			if (totalInvocations > 1)
				output.append("__" + invocationIndex + "__");
			return output.toString();
		}

		@Override
		public boolean hasReturnStatement() { return blockHasReturnStatement(ctx.block()); }

		@Override
		public String visitBody() {
			varStack.newBlock(params);
			structureStack.push(ContractStructure.MODIFIER_BODY);
			String output = visit(ctx.block());
			structureStack.pop();
			varStack.exitBlock();
			return output;
		}

		@Override
		public boolean hasOverride(SolidityContract callingContract) {
			boolean modifierFound = false;
			for (String parentName : callingContract.c3Linearization) {
				SolidityContract parent = contracts.get(parentName);
				for (SolidityModifier parentModifier : parent.modifiers) {
					if (parentModifier.name.equals(this.name) &&
							parameterListsAreEqual(parentModifier.getParamTypeNames(), this.getParamTypeNames())) {
						if (modifierFound) {
							return true;
						} else {
							modifierFound = true;
							break;
						}
					}
				}
			}
			return false;
		}
	}

	private class SolidityVariable {
		String name;
		String typename;
		boolean isConstant;

		SolidityVariable(String name, String typename) { this.name = name; this.typename = typename; }
		@Override public String toString() { return solidityToJavaType(typename) + " " + name; }

		public String getDisplayName(SolidityContract callingContract) {
			return name;
		}
	}

	private class SolidityField extends SolidityVariable {
		String ownerName;
		FieldVisibility visibility;
		SolidityParser.StateVariableDeclarationContext ctx;

		SolidityField(String name, String typename) { super(name, typename); }

		/**
		 * Get the name of the field as it would be displayed from the POV of 'callingContract'.
		 * I.e., if the field has been imported from another contract, the display name may contain
		 * as a prefix the name of the contract that originally defined the field.
		 * @param callingContract The contract in which the field should 'displayed'.
		 * @return The display name.
		 */
		public String getDisplayName(SolidityContract callingContract) {
			if (!this.ownerName.equals(callingContract.name) && this.hasOverride(callingContract)) {
				return "__" + currentOwnerContract.name + "__" + name;
			} else {
				return name;
			}
		}

		public boolean hasOverride(SolidityContract callingContract) {
			for (String parentName : callingContract.c3Linearization) {
				SolidityContract parent = contracts.get(parentName);
				SolidityField parentField = parent.getField(this.name);
				if (parentField != null && parentField != this) {
					return true;
				}
			}
			return false;
		}
	}

	private class SolidityEnum {
		String name;
		String ownerName;
		public SolidityEnum(String name, String ownerName) {
			this.name = name; this.ownerName = ownerName;
		}

		@Override
		public String toString() {
			return ownerName + "." + name;
		}
	}

	private class SolidityStruct {
		String name;
		String ownerName;
		List<SolidityVariable> fields = new LinkedList<>();
		public SolidityStruct(String name, String ownerName) {
			this.name = name; this.ownerName = ownerName;
		}

		@Override
		public String toString() {
			return ownerName + "." + name;
		}
	}

	private class SolidityContract {
		String name;
		ContractType type;
		boolean isAbstract;
		LinkedList<String> inheritanceList = new LinkedList<>();
		LinkedList<String> c3Linearization = new LinkedList<>();
		// The below are self-defined functions/fields/constructors, not inherited ones
		LinkedList<SolidityFunction> functions = new LinkedList<>();
		LinkedList<SolidityField> fields = new LinkedList<>();
		LinkedList<SolidityModifier> modifiers = new LinkedList<>();
		LinkedList<SolidityEnum> enums = new LinkedList<>();
		LinkedList<SolidityStruct> structs = new LinkedList<>();
		SolidityConstructor constructor;

		// The names of all libraries 'L' such that the declaration 'using L for *' is found within the contract.
		List<String> globalUsingForLibraries = new LinkedList<>();
		// The names of all library attachments made from Using For statements,
		//  for each type (contract, elementary type, struct), within the contract.
		//  The map is (type => libraries).
		Map<String, List<String>> typeLibAttachments = new HashMap<>();

		/**
		 * Collect all library functions attached to the given type inside this contract, given all its containing
		 * "Using For" declarations. The type could be elementary or a contract.
		 * @param type The type to check for it.
		 * @return A set of all the library functions for the type in this contract.
		 */
		List<SolidityFunction> getAttachedLibraryFunctionsForType(String type) {
			List<SolidityFunction> attachedLibFunctions = new LinkedList<>();
			for (String libName : currentOwnerContract.globalUsingForLibraries) {
				SolidityContract lib = contracts.get(libName);
				lib.functions.forEach(libFun -> {
					if (!attachedLibFunctions.contains(libFun))
						attachedLibFunctions.add(libFun);
				});
			}
			if (currentOwnerContract.typeLibAttachments.containsKey(type)) {
				for (String libName : currentOwnerContract.typeLibAttachments.get(type)) {
					SolidityContract lib = contracts.get(libName);
					lib.functions.forEach(libFun -> {
						if (!attachedLibFunctions.contains(libFun))
							attachedLibFunctions.add(libFun);
					});
				}
			}
			return attachedLibFunctions;
		}

		/**
		 * Given a function call with the supplied name and argument types, locate the corresponding function
		 * in this contract. Visibility does not matter. Note: use the method 'lookupFunction' to perform a name
		 * lookup instead, where the entire inheritance tree is searched (C3 linearization), and inherited, private
		 * functions are not returned (they cannot be seen from the perspective of outside this contract).
		 * @param funName The name of the function in the function call.
		 * @param argTypes The types of the supplied arguments.
		 * @param allowSubTyping Whether to allow argument types to be subtypes of function parameters
		 * @param allowImplicitConversions Whether to allow argument types to be implicitly convertible to function parameters.
		 * @return If it was found, the function, otherwise null.
		 */
		SolidityFunction getFunction(String funName,
									 List<String> argTypes,
									 boolean allowSubTyping,
									 boolean allowImplicitConversions)
		{
			for (SolidityFunction fun : functions) {
				if (fun.name.equals(funName)) {
					if (argTypesMatchesFunctionParams(argTypes, fun.getParamTypeNames(), fun, allowSubTyping, allowImplicitConversions))
						return fun;
				}
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

		SolidityModifier getModifier(String modName) {
			// Note: modifiers cannot be overloaded with different argument lists.
			for (SolidityModifier mod : modifiers) {
				if (mod.name.equals(modName))
					return mod;
			}
			return null;
		}

		SolidityEnum getEnum(String enumName) {
			int dotPos = enumName.indexOf(".");
			if (dotPos == -1) {
				for (SolidityEnum enum_ : enums) {
					if (enum_.name.equals(enumName))
						return enum_;
				}
			} else {
				if (enumName.substring(0, dotPos).equals(this.name)) {
					return getEnum(enumName.substring(dotPos + 1));
				}
			}
			return null;
		}

		SolidityStruct getStruct(String structName) {
			int dotPos = structName.indexOf(".");
			if (dotPos == -1) {
				for (SolidityStruct struct : structs) {
					if (struct.name.equals(structName))
						return struct;
				}
			} else {
				if (structName.substring(0, dotPos).equals(this.name)) {
					return getStruct(structName.substring(dotPos + 1));
				}
			}
			return null;
		}

		/**
		 * Given a function call with the supplied name and argument types, locate the corresponding function
		 * in the inheritance hierarchy (C3 linearization) of the contract given. Note: the corresponding
		 * 'getFunction' method only looks for the function in this contract.
		 * @param funName The name of the function in the function call.
		 * @param argTypes The types of the supplied arguments.
		 * @param allowSubTyping Whether to allow argument types to be subtypes of function parameters
		 * @param allowImplicitConversions Whether to allow argument types to be implicitly convertible to function parameters.
		 * @return If it was found, the function, otherwise null.
		 */
		SolidityFunction lookupFunction(String funName,
										List<String> argTypes,
										boolean allowSubTyping,
										boolean allowImplicitConversions)
		{
			Iterator<String> it = c3Linearization.descendingIterator();
			while (it.hasNext()) {
				SolidityContract parent = contracts.get(it.next());
				for (SolidityFunction fun : parent.functions) {
					if (fun.name.equals(funName) &&
							(fun.visibility != FunctionVisibility.PRIVATE || parent.name.equals(this.name)))
					{
						if (argTypesMatchesFunctionParams(argTypes, fun.getParamTypeNames(), fun, allowSubTyping, allowImplicitConversions))
							return fun;
					}
				}
			}
			return null;
		}

		SolidityField lookupField(String fieldName) {
			Iterator<String> it = c3Linearization.descendingIterator();
			while (it.hasNext()) {
				SolidityContract parent = contracts.get(it.next());
				for (SolidityField field : parent.fields) {
					if (field.name.equals(fieldName))
						return field;
				}
			}
			return null;
		}

		SolidityModifier lookupModifier(String modName) {
			// Note: modifiers cannot be overloaded with different argument lists.
			Iterator<String> it = c3Linearization.descendingIterator();
			while (it.hasNext()) {
				SolidityContract parent = contracts.get(it.next());
				for (SolidityModifier mod : parent.modifiers) {
					if (mod.name.equals(modName))
						return mod;
				}
			}
			return null;
		}

		SolidityEnum lookupEnum(String enumName) {
			/*
				contract A { enum E {e} }
				contract B is A {
					function foo() public {
						A a = new A();
						E e1 = E.e; // allowed
						A.E e2 = A.E.e; // allowed
						a.E e3 = A.E.e; // disallowed
					}
				}
				contract C {
					function foo() public {
						A a = new A();
						E e1 = E.e; // disallowed
						A.E e2 = A.E.e; // allowed
						B.E e3 = B.E.e; // disallowed
					}
				}
			 */
			int dotPos = enumName.indexOf(".");
			if (dotPos == -1) {
				Iterator<String> it = c3Linearization.descendingIterator();
				while (it.hasNext()) {
					SolidityContract parent = contracts.get(it.next());
					for (SolidityEnum enum_ : parent.enums) {
						if (enum_.name.equals(enumName))
							return enum_;
					}
				}
			} else {
				SolidityContract contract = contracts.get(enumName.substring(0, dotPos));
				if (contract == null) {
					return null;
				}
				return contract.getEnum(enumName.substring(dotPos + 1));
			}
			return null;
		}

		SolidityStruct lookupStruct(String structName) {
			// Similar rules as for enums
			int dotPos = structName.indexOf(".");
			if (dotPos == -1) {
				Iterator<String> it = c3Linearization.descendingIterator();
				while (it.hasNext()) {
					SolidityContract parent = contracts.get(it.next());
					for (SolidityStruct struct : parent.structs) {
						if (struct.name.equals(structName))
							return struct;
					}
				}
			} else {
				SolidityContract contract = contracts.get(structName.substring(0, dotPos));
				if (contract == null) {
					return null;
				}
				return contract.getStruct(structName.substring(dotPos + 1));
			}
			return null;
		}

		/**
		 * Get the name of the contract before (less derived) the supplied contract in this contract's linearization list.
		 * @param contractName The name of the contract that should be after the contract this is returned.
		 * @return The contract before the one given by 'contractName', in the linearization list of this coontract.
		 */
		String getContractBefore(String contractName) {
			Iterator<String> it = c3Linearization.descendingIterator();
			while (it.hasNext()) {
				String parentName = it.next();
				if (parentName.equals(contractName)) {
					if (it.hasNext())
						return it.next();
					return null;
				}
			}
			return null;
		}

		boolean hasNonDefaultConstructor() {
			return this.constructor != null && !this.constructor.isDefaultConstructor();
		}

		@Override
		public String toString() {
			return "Contract " + name + "; \n Inheritance list: " + inheritanceList.toString() +
					"\nlinearization: " + c3Linearization.toString() + "\nFunctions: " +
					functions.toString() + "\nFields: " + fields.toString();
		}

		public String getDisplayName() { return name + "Impl"; }
	}

	/**
	 * Use this class to maintain an environment during the visiting;
	 * we have a stack of scope, where each scope has a list of variables defined in that scope.
	 * The outermost scope contains the fields of the current contract.
	 */
	private class VariableScopeStack {
		private final Deque<LinkedList<SolidityVariable>> deque = new ArrayDeque<>();

		/**
		 * Reset the stack to only include the fields of the current owner contract (and its inherited fields).
		 */
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

		public <T extends SolidityVariable> void pushVar(T var) {
			LinkedList<SolidityVariable> topContext = deque.peekFirst();
			if (topContext == null)
				error("Tried to declare a variable when outside of any scope.");
			topContext.add(var);

		}

		public void clear() {
			deque.clear();
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
					if (var.name.equals(identifier) || var.getDisplayName(currentContract).equals(identifier)) {
						return var;
					}
				}
			}
			return null;
		}

		public SolidityField getFieldFromIdentifier(String identifier) {
			for (LinkedList<SolidityVariable> scope : deque) {
				for (SolidityVariable var : scope) {
					if (var instanceof SolidityField &&
							(var.name.equals(identifier) || var.getDisplayName(currentContract).equals(identifier))) {
						return (SolidityField) var;
					}
				}
			}
			return null;
		}

		public String getTypeofIdentifier(String identifier) {
			SolidityVariable var = getVariableFromIdentifier(identifier);
			return var == null ? null : var.typename;
		}

		@Override public String toString() {
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

	/**
	 * Contains details about the modifier flattening process, if it is currently taking place.
	 */
	private static class ModifierFlattening {
		static boolean isActive = false;
		static ModifierFlatteningMode mode;
		static SolidityCallable mainCallable;
		static String braceFreeMainCallableBodyOutput;
		static String parentConstructorCallsOutput;
		static List<SolidityModifier> currentModList;
		static int currentModPos;

		/**
		 * During flattening when modifiers invoke other modifiers, we have to pass the original function's/constructor's
		 * parameters with every modifier call. Use this function to rename these parameters, as they are displayed
		 * in the modifier headers and bodies, so that their names do not clash with the names of the actual modifier parameters.
		 * @param paramName The original name of the parameter.
		 * @return The name of the parameter as it would be displayed in the modifier header/body.
		 */
		static String getDisplayNameOfCallableParamInModifier(String paramName) {
			return "__" + mainCallable.name + "__" + paramName;
		}
	}

	/**
	 * An instance of this class is returned after we have performed function/modifier overload/override resolution.
	 * 'callable' is the actual function/modifier that the resolution resulted in, and 'displayedName' shows
	 * how the function/modifier should be displayed from where it was called.
	 */
	private class CallableOverloadResolutionResult {
		String displayedName;
		SolidityCallable callable;
		SolidityField field; // A function call may actually be a call to a getter for a field.
		FunctionCallReferenceType referenceType;
		CallableOverloadResolutionResult(String displayedName, SolidityCallable callable,
										 SolidityField field, FunctionCallReferenceType referenceType)
		{
			this.displayedName = displayedName; this.callable = callable;
			this.field = field; this.referenceType = referenceType;
		}
	}

	/**
	 * An instance of this class is returned after we have performed function/constructor modifier flattening.
	 * 'mainBody' contains the output for the main body of the resulting method/constructor, i.e., the one that is
	 * visible from outside the contract class, and 'externalFunction' contains the output of additional methods
	 * that were created in the process (still part of the contract output, but external to the original function).
	 */
	private class CallableFlatteningResult {
		String mainBodyOutput;
		String externalMethodsOutput;
		CallableFlatteningResult() {}
		CallableFlatteningResult(String mainBodyOutput, String externalMethodsOutput) {
			this.mainBodyOutput = mainBodyOutput; this.externalMethodsOutput = externalMethodsOutput;
		}
	}

	private boolean implicitTypeConversionIsAllowed(String typeFrom, String typeTo) {
		// TODO: not complete
		if (typeFrom.equals(typeTo))
			return true;

		switch (typeFrom) {
			case "int" -> {
				if (typeTo.equals("int256"))
					return true;
			}
			case "uint" -> {
				if (typeTo.equals("uint256") || typeTo.equals("int"))
					return true;
			}
			case "int256" -> {
				if (typeTo.equals("int"))
					return true;
			}
			case "uint256" -> {
				if (typeTo.equals("uint"))
					return true;
			}
			case "address payable" -> {
				if (typeTo.equals("address"))
					return true;
			}
			default -> {
				return false;
			}
		}
		return false;
	}

	private boolean nameIsAContract(String name) {
		return contracts.get(name) != null;
	}

	private boolean typeIsElementary(String type) { return !nameIsAContract(type); }

	private boolean typeIsArray(String type) {
		return type.endsWith("[]") || type.startsWith("bytes") || type.equals("string");
	}

	/**
	 * Compare two parameter lists. Only the types are compared, not the names. Subtypes are not allowed, i.e.,
	 * if B is A, then params1[0] == A and params2[1] == B is not allowed. This is because this function is used to
	 * check for function overrides, but in the above example, functions with such parameter lists do not override.
	 * Implicit type conversions are also not allowed.
	 * @param params1 The first parameter list.
	 * @param params2 The second parameter list.
	 * @return True if the lists' types are the same, otherwise false.
	 */
	private boolean parameterListsAreEqual(List<String> params1, List<String> params2) {
		if (params1.size() != params2.size())
			return false;
		int index = -1;
		for (String type : params1) {
			++index;
			if (!type.equals(params2.get(index)))
				return false;
		}
		return true;
	}

	/**
	 * Compare two parameter list to check if the types supplied in 'callArgTypes' are admissible in a call to a
	 * function with parameter list 'funParamTypes'.
	 * @param callArgTypes The argument types given with a function call.
	 * @param funParamTypes The parameter list of a function.
	 * @param callable The function/constructor/modifier with the parameter.
	 * @param allowSubTyping If T2 is a subtype of T1, is the call admissible if the parameter type is T1 and the
	 *                       argument type is T2?
	 * @param allowImplicitConversions If T2 can be implicitly converted to T1, is the call admissible if the parameter
	 *                                 type is T1 and the argument type is T2?
	 * @return True if the types align so that the function could be called with the arguments given in the function call.
	 */
	private boolean argTypesMatchesFunctionParams(List<String> callArgTypes,
												  List<String> funParamTypes,
												  SolidityCallable callable,
												  boolean allowSubTyping,
												  boolean allowImplicitConversions) {
		if (funParamTypes.size() != callArgTypes.size())
			return false;
		int index = -1;
		for (String argType : callArgTypes) {
			++index;
			String paramType = funParamTypes.get(index);
			if (!argTypeMatchesFunctionParam(argType, paramType, callable, allowSubTyping, allowImplicitConversions))
				return false;
		}
		return true;
	}

	/**
	 * Compare an argument type with a parameter type to see if they match.
	 * @param callArgType The argument type given with a function call.
	 * @param funParamType The parameter type of a function.
	 * @param callable The function/constructor/modifier with the parameter.
	 * @return True if the types align so that the function could be called with the arguments given in the function call.
	 */
	private boolean argTypeMatchesFunctionParam(String callArgType,
												String funParamType,
												SolidityCallable callable,
												boolean allowSubTyping,
												boolean allowImplicitConversions)
	{
		if (callArgType.equals(funParamType)) {
			return true;
		}
		if (allowSubTyping && nameIsAContract(callArgType) && nameIsAContract(funParamType)) {
			// Allow for polymorphism; check for subtypes
			return contracts.get(callArgType).c3Linearization.contains(funParamType);
		}

		// Check if the types are enums
		SolidityEnum enum1 = currentOwnerContract.lookupEnum(callArgType);
		SolidityEnum enum2 = contracts.get(callable.ownerName).lookupEnum(funParamType);
		if (enum1 != null && enum2 != null) {
			return enum1.name.equals(enum2.name) && enum1.ownerName.equals(enum2.ownerName);
		} else if (enum1 != null || enum2 != null) {
			return false;
		}
		// Check if the types are structs
		SolidityStruct struct1 = currentOwnerContract.lookupStruct(callArgType);
		SolidityStruct struct2 = contracts.get(callable.ownerName).lookupStruct(funParamType);
		if (struct1 != null && struct2 != null) {
			return struct1.name.equals(struct2.name) && struct1.ownerName.equals(struct2.ownerName);
		} else if (struct1 != null || struct2 != null) {
			return false;
		}

		if (allowImplicitConversions) {
			return implicitTypeConversionIsAllowed(callArgType, funParamType);
		}
		return false;
	}

	/**
	 * Checks whether a function identifier is a reserved Solidity function name, e.g., 'require', and if so,
	 * returns the return type of that function. This is in the context of a contract; the name before the first dot
	 * should be something that is visible from inside the given contract.
	 * @param name The function name, with any number of qualifiers (dots).
	 * @param containingContract The contract in which the name was referenced (e.g., function call was made)
	 * @param checkLocalVars Whether to check if the first name (before the first dot) is a local variable in the
	 *                       current context.
	 * @return If the function name is reserved, the Solidity return type of the function. Else, an empty Optional.
	 */
	private Optional<String> getReservedFunctionReturnTypeContractContext(String name, SolidityContract containingContract, boolean checkLocalVars) {
		int firstDotPos = name.indexOf(".");
		if (firstDotPos == -1) {
			String retType = reservedFreeFunctions.get(name);
			return retType == null ? Optional.empty() : Optional.of(retType);
		}
		String beforeFirstDot = name.substring(0, firstDotPos);
		String afterFirstDot = name.substring(firstDotPos + 1);
		if (checkLocalVars) {
			SolidityVariable var = varStack.getVariableFromIdentifier(beforeFirstDot);
			if (var != null) {
				if (nameIsAContract(var.typename)) {
					return getReservedFunctionReturnTypeContractContext(afterFirstDot, contracts.get(var.typename), false);
				}
				SolidityStruct struct = containingContract.lookupStruct(var.typename);
				if (struct != null) {
					return getReservedFunctionReturnTypeStructContext(afterFirstDot, struct);
				}
				return getReservedFunctionReturnTypeElementaryTypeContext(afterFirstDot, var.typename);
			}
		}
		SolidityField field = containingContract.lookupField(beforeFirstDot);
		if (field != null) {
			if (nameIsAContract(field.typename)) {
				return getReservedFunctionReturnTypeContractContext(afterFirstDot, contracts.get(field.typename), false);
			}
			SolidityStruct struct = containingContract.lookupStruct(field.typename);
			if (struct != null) {
				return getReservedFunctionReturnTypeStructContext(afterFirstDot, struct);
			}
			return getReservedFunctionReturnTypeElementaryTypeContext(afterFirstDot, field.typename);
		}
		if (nameIsAContract(beforeFirstDot))
			return getReservedFunctionReturnTypeContractContext(afterFirstDot, contracts.get(beforeFirstDot), false);
		if (beforeFirstDot.equals("this"))
			return getReservedFunctionReturnTypeContractContext(afterFirstDot, containingContract, false);
		if (beforeFirstDot.equals("msg")) {
			return getReservedFunctionReturnTypeMsgContext(afterFirstDot);
		}
		// Note: if the prefix is "super", this won't be a reserved function; only parent functions can be called that way.
		return Optional.empty();
	}

	/**
	 * Checks whether a function identifier is a reserved Solidity function name, e.g., 'require', and if so,
	 * returns the return type of that function. This is in the context of an elementary type; we are looking for
	 * reserved functions that can be referenced from a variable or field of an elementary type.
	 * Example: a.transfer(...), where 'a' is a variable of type address. This function would then be called with 'name'
	 * being equal to "transfer(...)"
	 * @param name The function name, with any number of qualifiers.
	 * @param elementaryType The type of the field or local variable that we are currently looking in.
	 *                       Example: we are initially given the expression "a.transfer(...)". 'exp' would then be
	 *                       "transfer(...)", and elementary type would be "address".
	 * @return If the function name is reserved, the Solidity return type of the function. Else, an empty Optional.
	 */
	private Optional<String> getReservedFunctionReturnTypeElementaryTypeContext(String name, String elementaryType) {
		int firstDotPos = name.indexOf('.');
		String beforeFirstDot = firstDotPos == -1 ? name : name.substring(0, firstDotPos);
		String afterFirstDot = firstDotPos == -1 ? name : name.substring(firstDotPos + 1);
		String retType = null;
		if (elementaryType.equals("address")) {
			retType = reservedAddressFunctions.get(beforeFirstDot);
		} else if (elementaryType.equals("string")) {
			retType = reservedStringFunctions.get(beforeFirstDot);
		} else if (elementaryType.startsWith("bytes")) {
			retType = reservedBytesFunctions.get(beforeFirstDot);
		} else if (typeIsArray(elementaryType)) {
			retType = reservedArrayFunctions.get(beforeFirstDot);
		}
		if (retType == null) {
			return Optional.empty();
		} else if (firstDotPos == -1) {
			return Optional.of(retType);
		} else {
			// The field can only be of an elementary type.
			return getReservedFunctionReturnTypeElementaryTypeContext(afterFirstDot, retType);
		}
	}

	/**
	 * Checks whether a function identifier is a reserved Solidity function name, e.g., 'require', and if so,
	 * returns the return type of that function. This is in the context of the global variable "msg"; we are looking
	 * for reserved function that can be referenced starting from the msg variable.
	 * Example: msg.sender.transfer(...); This function would then be called with 'name' being equal to "sender.transfer(...)"
	 * @param name The function name, with any number of qualifiers.
	 * @return If the function name is reserved, the Solidity return type of the function. Else, an empty Optional.
	 */
	private Optional<String> getReservedFunctionReturnTypeMsgContext(String name) {
		int firstDotPos = name.indexOf('.');
		if (firstDotPos == -1) // there are no functions in 'msg'; we must have at least one field, then a function.
			return Optional.empty();
		String beforeFirstDot = name.substring(0, firstDotPos);
		String afterFirstDot = name.substring(firstDotPos + 1);
		String msgFieldType = reservedMsgFields.get(beforeFirstDot);
		if (msgFieldType == null)
			return Optional.empty();
		// The field can only be of an elementary type
		return getReservedFunctionReturnTypeElementaryTypeContext(afterFirstDot, msgFieldType);
	}

	/**
	 * Checks whether a function identifier is a reserved Solidity function name, e.g., 'require', and if so,
	 * returns the return type of that function. This is in the context of a struct; we are looking for
	 * reserved functions that can be referenced from an instance of a struct.
	 * Example: s.a.transfer(...), where 's' is a struct instance, and 'a' is a variable of type address in that struct.
	 * This function would then be called with 'name' equal to 'a.transfer(...)', and containingStruct would be the
	 * struct that 's' is an instance of.
	 * @param name The function name, with any number of qualifiers.
	 * @param containingStruct The struct in which the name was referenced (e.g., function call was made)
	 * @return If the function name is reserved, the Solidity return type of the function. Else, an empty Optional.
	 */
	private Optional<String> getReservedFunctionReturnTypeStructContext(String name, SolidityStruct containingStruct) {
		int firstDotPos = name.indexOf(".");
		if (firstDotPos == -1) {
			// Structs do not have reserved functions.
			return Optional.empty();
		}
		String beforeFirstDot = name.substring(0, firstDotPos);
		String afterFirstDot = name.substring(firstDotPos + 1);
		for (SolidityVariable var : containingStruct.fields) {
			if (var.name.equals(beforeFirstDot)) {
				if (nameIsAContract(var.typename))
					return getReservedFunctionReturnTypeContractContext(afterFirstDot, contracts.get(var.typename), false);
				SolidityStruct struct = contracts.get(containingStruct.ownerName).lookupStruct(var.typename);
				if (struct != null)
					return getReservedFunctionReturnTypeStructContext(afterFirstDot, struct);
				return getReservedFunctionReturnTypeElementaryTypeContext(afterFirstDot, var.typename);
			}
		}
		return Optional.empty();
	}
	/**
	 * Checks whether we are currently visiting a function/field/constructor/modifier that was inherited.
	 * @return The result of currentContract != currentOwnerContract.
	 */
	private boolean currentlyVisitingInheritedMember() { return currentContract != currentOwnerContract; }

	/**
	 * Make a conversion between a Solidity type and a Java type.
	 * @param solidityTypeName The name of the type in Solidity
	 * @return The name of the type in Java (as it is translated).
	 */
	private String solidityToJavaType(String solidityTypeName) {
		String javaTypeName = solidityTypeName.replace(" ", "");
		switch (solidityTypeName) {
			case "uint", "uint256", "bytes32" -> javaTypeName = "int";
			case "bool" -> javaTypeName = "boolean";
			case "string" -> javaTypeName = "String";
			case "address" -> javaTypeName = "Address";
			case "address[]" -> javaTypeName = "Address[]";
			case "uint[]" -> javaTypeName = "int[]";
			case "uint256[]" -> javaTypeName = "int[]";
			case "bytes32[]" -> javaTypeName = "int[]";
			case "mapping(address=>uint)" -> javaTypeName = "int[]";
			case "mapping(address=>uint256)" -> javaTypeName = "int[]";
			case "mapping(uint=>uint)" -> javaTypeName = "int[]";
			case "mapping(uint256=>uint256)" -> javaTypeName = "int[]";
			case "mapping(uint=>address)" -> javaTypeName = "Address[]";
			case "mapping(uint256=>address)" -> javaTypeName = "Address[]";
			case "mapping(address=>bool)" -> javaTypeName = "boolean[]";
			case "mapping(uint=>bool)" -> javaTypeName = "boolean[]";
			case "mapping(uint256=>bool)" -> javaTypeName = "boolean[]";
			case "mapping(address=>string)" -> javaTypeName = "String[]";
			case "mapping(uint=>string)" -> javaTypeName = "String[]";
			case "mapping(uint256=>string)" -> javaTypeName = "String[]";
			default -> {
			}
		}
		return javaTypeName;
	}

	private boolean blockHasReturnStatement(SolidityParser.BlockContext blockCtx) {
		SolidityCallableHasReturnStatementVisitor visitor = new SolidityCallableHasReturnStatementVisitor();
		return visitor.visit(blockCtx);
	}

	/**
	 * The default value of a type, as it would be in SolidiKeY, not Java. For instance, the default value of 'string'
	 * is "", not null.
	 * @param typeName The name of type in either Solidity or Java (it is converted to a Java type).
	 * @return The default value of the type in Solidity, as a string.
	 */
	private String defaultValueOfType(String typeName) {
		// TODO: for int[], the default value should be "new int[n]" (Solidity default initialization),
		//  where n is the size, but we don't know the size.
		if (nameIsAContract(typeName)) {
			return "new " + contracts.get(typeName).getDisplayName() + "()";
		}
		SolidityStruct struct = currentOwnerContract.getStruct(typeName);
		if (struct != null) {
			return "new " + struct + "()";
		}
		return switch (solidityToJavaType(typeName)) {
			case "int" -> "0";
			case "boolean" -> "false";
			case "String" -> "\"\"";
			case "Address" -> "new Address()"; // TODO: not sure if Address has a constructor like this
			default -> "null";
		};
	}

	private String removeOuterBracesFromCallableBodyOutput(String callableBodyOutput) {
		int openIndex = callableBodyOutput.indexOf('{');
		if (openIndex == -1)
			error("Supplied body does not have an opening brace.");
		int endIndex = callableBodyOutput.lastIndexOf('}');
		if (endIndex == -1)
			error("Supplied body does not have an ending brace");
		return callableBodyOutput.subSequence(openIndex + 1, endIndex).toString();
	}

	/**
	 * Resolve a function call; given the function call expression context and the contract from which the function
	 * was called, perform overload resolution to determine which explicit function should be called.
	 * @param ctx The function call expression context.
	 * @return A tuple of 1) the name of the explicit function that is called, as it should be displayed in
	 *                       the current contract, and
	 *                    2) the function itself as a 'SolidityFunction', containing e.g. the context and signature.
	 *                       If the function was actually a getter of a field, the field is returned.
	 */
	private CallableOverloadResolutionResult resolveFunctionCall(SolidityParser.FunctionCallExpressionContext ctx) {
		/* We have six different types of "function calls", one of them a constructor call, where overload resolution
		   is not actually done. 'C' is a contract/library name, and 'c' is an instance of a contract/struct/elementary type.
		   During overload resolution, we walk up the linearization tree, starting from a
		   given contract, to find a suitable function. The below table lists whose linearization
		   list we use in which cases, and from where we start walking.

		   We also need to consider whether we are calling a library function, which has been attached to the current
		   object (contract, struct, or elementary type).

		   Note that, in every function call type below, except internal and constructor, 'foo' may actually refer
		   to a field (this is invoking an automatically-generated getter for that field).

		   Note: s.super.foo() is not allowed.
		   Note: the below does not include calls to modifiers. Those go through 'visitFunctionDefinition' and
		   'visitConstructorDefinition' instead, where a modifier body is visited if it is invoked.
		Type					Example			Linearization owner		Linearization walk starting contract.
		internal				foo()			currentContract			currentContract
		external, direct: 		C.foo()			currentContract			C. foo must be in C
		external, instance: 	c.foo()			typeof(c)				typeof(c)
		this					this.foo()		================== Same as internal ==================
		super					super.foo()		currentContract			the contract before currentOwnerContract
		constructor				C()				does not apply			does not apply
		 */
		// TODO: we may not call an external function unless 'this' is used. Currently, this is not checked,
		//  and could lead to function overload resolution being wrong in very specific situations (?)

		String fctName = ctx.expression().getText();
		String objectName = fctName;
		String comparableName = fctName;
		// Find the type of function call (above table)
		FunctionCallReferenceType referenceType;
		boolean isConstructorCall = false;
		int firstDotPos = fctName.indexOf('.');
		if (firstDotPos == -1) {
			referenceType = FunctionCallReferenceType.INTERNAL;
			// TODO: Currently, calls such as "new A()" gets turned into a function call to "newA". Fix?
			// Currently, Solidity allows one to use "new" only on contract types and arrays.
			isConstructorCall = fctName.startsWith("new") &&
					(nameIsAContract(fctName.substring("new".length())) || typeIsArray(fctName.substring("new".length())));
		} else {
			objectName = fctName.substring(0, firstDotPos);
			comparableName = fctName.substring(firstDotPos + 1);
			if (objectName.equals("this")) {
				referenceType = FunctionCallReferenceType.THIS;
			} else if (objectName.equals("super")) {
				referenceType = FunctionCallReferenceType.SUPER;
			} else if (nameIsAContract(objectName)) {
				if (contracts.get(objectName).type == ContractType.LIBRARY)
					referenceType = FunctionCallReferenceType.LIBRARY;
				else
					referenceType = FunctionCallReferenceType.CONTRACT;
			} else if (varStack.getVariableFromIdentifier(objectName) != null) {
				referenceType = FunctionCallReferenceType.OBJECT;
			} else if (objectName.equals("msg")) {
				return new CallableOverloadResolutionResult(fctName, null, null, FunctionCallReferenceType.OBJECT);
			} else {
				error("Could not locate name " + objectName + " during overload resolution of function " + fctName);
				return null;
			}
		}

		if (isConstructorCall) {
			// Since a contract can have at most one constructor, there is no need to resolve overloads.
			// TODO: Currently, calls such as "new A()" gets turned into a function call to "newA". Change somehow?
			String type = fctName.substring("new".length());
			if (nameIsAContract(type)) {
				String ownerContractName = fctName.substring("new".length());
				SolidityContract ownerContract = contracts.get(ownerContractName);
				if (ownerContract == null)
					error("Could not locate contract " + ownerContractName);
				String displayName = "new " + ownerContract.getDisplayName();
				return new CallableOverloadResolutionResult(displayName, ownerContract.constructor, null, referenceType);
			} else if (typeIsElementary(type)) {
				String displayName = "new " + solidityToJavaType(type);
				return new CallableOverloadResolutionResult(displayName, null, null, referenceType);
			} else {
				error("Could not resolve constructor call " + fctName + " in contract " + currentOwnerContract.name);
			}
		}

		// Get the argument list types from the call.
		LinkedList<String> resolvedArgs = new LinkedList<>();
		if (ctx.functionCallArguments().expressionList() != null) {
			for (SolidityParser.ExpressionContext exprCtx : ctx.functionCallArguments().expressionList().expression()) {
				// Get the type of the expression
				SolidityExpressionTypeVisitor typeVisitor = new SolidityExpressionTypeVisitor();
				String typename = typeVisitor.visit(exprCtx);
				resolvedArgs.add(typename);
			}
		}

		// If a library function was called (directly, without the 'Using For' construct, and from outside the library),
		//  lookup the function there
		if (referenceType == FunctionCallReferenceType.LIBRARY) {
			SolidityContract library = contracts.get(objectName);
			SolidityFunction libFun = library.getFunction(comparableName, resolvedArgs, true, true);
			if (libFun == null) {
				error("Could not find function " + comparableName + " in library " + library.name);
			} else {
				String displayedName = library.name + "." + libFun.name;
				return new CallableOverloadResolutionResult(displayedName, libFun, null, referenceType);
			}
		}

		// Look for calls to attached library functions (these come from "Using For" declarations).
		//  Here, the first parameter of the original library function should be missing in the argument list,
		//  if that parameter's type was the same as the type of the object the function was called on.
		//  This is so that the function can be called as a member function, and the first parameter is implicit.
		String typeOfThis = switch (referenceType) {
			case INTERNAL, THIS -> currentOwnerContract.name;
			case CONTRACT -> objectName;
			case SUPER -> currentContract.getContractBefore(currentOwnerContract.name);
			case OBJECT -> varStack.getTypeofIdentifier(objectName);
			default -> error("Unrecognizable function call reference type.");
		};
		List<String> resolvedArgsPrependedWithThis = new LinkedList<>(resolvedArgs);
		resolvedArgsPrependedWithThis.add(0, typeOfThis);

		for (SolidityFunction libFun : currentOwnerContract.getAttachedLibraryFunctionsForType(typeOfThis)) {
			if (libFun.name.equals(comparableName) &&
					argTypesMatchesFunctionParams(resolvedArgsPrependedWithThis, libFun.getParamTypeNames(), libFun, true, true)) {
				String displayedName = libFun.ownerName + "." + libFun.name;
				return new CallableOverloadResolutionResult(displayedName, libFun, null, referenceType);
			}
		}

		// No library functions were found. If the object type is elementary, at this point, no more functions remain
		if (referenceType == FunctionCallReferenceType.OBJECT && typeIsElementary(typeOfThis)) {
			error("Could not resolve function call " + fctName +  " in contract " + currentOwnerContract.name);
		}

		// Perform the linearization walk to look for self-defined or inherited functions.
		SolidityContract caller; // Whose linearization to use.
		String startContractName; // The walking of the linearization list should start from this contract.
		if (referenceType == FunctionCallReferenceType.OBJECT) {
			String typeName = varStack.getTypeofIdentifier(objectName);
			if (nameIsAContract(typeName)) {
				caller = contracts.get(typeName);
			} else {
				// linearization walking will not be performed
				error("Could not resolve function call " + fctName + " in contract " + currentOwnerContract.name);
				caller = null;
			}
		} else {
			caller = currentContract;
		}
		if (referenceType == FunctionCallReferenceType.SUPER) {
			startContractName = currentOwnerContract.name;
		} else if (referenceType == FunctionCallReferenceType.CONTRACT) {
			startContractName = objectName;
		} else {
			startContractName = caller.name;
		}
		/* When we walk up the linearization list, we must first find the contract 'startContract',
		   which is from where the actual searching after the function starts.
		   'skipSearchInStartContract' indicates whether we are allowed to search for the function
		   in 'startContract', once we locate 'startContract'.
		 */
		boolean startContractFound = false;
		boolean skipSearchInStartContract = referenceType == FunctionCallReferenceType.SUPER;
		SolidityFunction resolvedFun = null;
		SolidityField resolvedField = null;
		String displayName = null;
		Iterator<String> reverseIt = caller.c3Linearization.descendingIterator();
		while (reverseIt.hasNext()) {
			String parentName = reverseIt.next();
			if (!startContractFound) {
				if (parentName.equals(startContractName)) {
					startContractFound = true;
					if (skipSearchInStartContract) {
						continue;
					}
				} else {
					continue;
				}
			}
			SolidityContract parentContract = contracts.get(parentName);
			// Check if the parent has the function
			SolidityFunction fun = parentContract.getFunction(comparableName, resolvedArgs, true, true);
			if (fun != null) {
				boolean funIsVisible = fun.visibility != FunctionVisibility.PRIVATE ||
						(referenceType == FunctionCallReferenceType.OBJECT && caller.name.equals(currentOwnerContract.name)) ||
						(referenceType != FunctionCallReferenceType.OBJECT && parentName.equals(caller.name));
				if (!funIsVisible)
					continue;
				resolvedFun = fun;
				String funPrefix;
				if (referenceType == FunctionCallReferenceType.THIS) {
					funPrefix = "this.";
				} else if (referenceType == FunctionCallReferenceType.OBJECT) {
					SolidityVariable var = varStack.getVariableFromIdentifier(objectName);
					funPrefix = var.getDisplayName(currentContract) + ".";
				} else {
					funPrefix = "";
				}
				displayName = funPrefix + resolvedFun.getDisplayName(caller);
				break;
			}
			// Check if the parent has the field (getter)
			if (resolvedArgs.isEmpty()) {
				SolidityField field = parentContract.getField(comparableName);
				if (field != null) {
					boolean fieldIsVisible = field.visibility != FieldVisibility.PRIVATE ||
							(referenceType == FunctionCallReferenceType.OBJECT && caller.name.equals(currentOwnerContract.name)) ||
							(referenceType != FunctionCallReferenceType.OBJECT && parentName.equals(caller.name));
					if (!fieldIsVisible)
						continue;
					resolvedField = field;
					displayName = resolvedField.getDisplayName(caller);
					if (referenceType == FunctionCallReferenceType.OBJECT) {
						SolidityVariable var = varStack.getVariableFromIdentifier(objectName);
						displayName = var.getDisplayName(currentContract) + "." + displayName;
					}
				}
			}
		}
		if (resolvedFun == null && resolvedField == null) {
			error("Could not resolve function call for function " + comparableName +
					" from contract " + caller.name);
		}
		return new CallableOverloadResolutionResult(displayName, resolvedFun, resolvedField, referenceType);
	}

	/**
	 * Resolve a modifier call; given the modifier invocation context and the contract from which the modifier was called,
	 * perform overload (technically override; modifiers cannot be overloaded) resolution to determine which explicit
	 * modifier should be called.
	 * @param ctx The modifier invocation context.
	 * @return A tuple of 1) the name of the explicit modifier that is called, as it should be displayed in
	 *                       the current contract, and
	 *                    2) the modifier itself as a 'SolidityModifier', containing e.g. the context and signature.
	 */
	private CallableOverloadResolutionResult resolveModifierCall(SolidityParser.ModifierInvocationContext ctx) {
		String modName = ctx.identifier().getText();
		String comparableName = modName;
		String contractName = modName;
		int dotPos = modName.lastIndexOf('.');
		boolean isDirectCall = dotPos != -1;
		FunctionCallReferenceType referenceType;
		if (isDirectCall) {
			referenceType = FunctionCallReferenceType.CONTRACT;
			contractName = modName.substring(0, dotPos);
			comparableName = modName.substring(dotPos + 1);
		} else {
			referenceType = FunctionCallReferenceType.INTERNAL;
		}

		SolidityModifier mod;
		if (isDirectCall) {
			SolidityContract parent = contracts.get(contractName);
			if (parent == null) {
				error("Contract " + currentOwnerContract.name + " calls modifier " + modName +
						", but contract " + contractName + " does not exist.");
			}
			if (!currentOwnerContract.c3Linearization.contains(parent.name)) {
				error("Contract " + currentOwnerContract.name + " calls modifier " + modName +
						", but " + currentOwnerContract.name + " does not inherit from " + contractName);
			}
			mod = parent.getModifier(comparableName);

		} else {
			// We look in the current contract, not current owner contract. This is because, if a child has overridren
			// a modifier that is in the parent, and the parent has a function 'function foo() mod public {}',
			// then when that function is called from within the child, regardless of whether that function has
			// been overridden by the child or not, the function will use the child's version of the modifier, not
			// the parent's. Moreover, modifier cannot be overloaded in any way; if the parent function calls 'mod'
			// that takes no arguments, and the child defines a modifier with the same name, but that takes arguments,
			// this is not allowed. Thus, the correct modifier will be found by only looking at the modifier name,
			// not its arguments as part of the invocation.
			mod = currentContract.lookupModifier(modName);
		}
		if (mod != null) {
			String displayName = mod.getDisplayName(currentContract);
			return new CallableOverloadResolutionResult(displayName, mod, null, referenceType);
		}
		error("Contract " + contractName + " does not contain the modifier " + modName);
		return null;
	}

	/**
	 * "Flatten" a constructor or function by "baking in" its modifier and parent contract constructor invocations
	 * into the function body itself. This is done by creating an inner class in the function/constructor,
	 * and a function in this class is created for each modifier invocation. These functions are then called from
	 * inside the function in the order of the modifier list. Finally, the function itself is called
	 * (without modifiers). Constructor invocations simply become calls to external functions whose output have been
	 * created elsewhere. These calls are in the order of the current contract's C3 linearization, and are made
	 * before the modifiers are called.
	 * @param callable The constructor or function for which to perform the flattening for.
	 * @param braceFreeCallableBodyOutput The output for the main callable body, without the outer braces.
	 * @param parentConstructorCallsOutput The output for the parent constructor calls, as it should be part of the
	 *                                     main function body.
	 * @param modCtxs A list of modifier invocations.
	 * @return The Java output for the flattened method/constructor body, as well as Java output for possible
	 * external methods that were created.
	 */
	private CallableFlatteningResult createFlattenedCallable(SolidityCallable callable,
															 String braceFreeCallableBodyOutput,
															 String parentConstructorCallsOutput,
															 List<SolidityParser.ModifierInvocationContext> modCtxs) {
		StringBuilder mainBodyOutput = new StringBuilder("{\n");

		// If the modifier list does not contain any actual modifiers, add the constructor and body output and return.
		if (modCtxs == null || modCtxs.isEmpty()) {
			mainBodyOutput.append(parentConstructorCallsOutput);
			mainBodyOutput.append(braceFreeCallableBodyOutput);
			mainBodyOutput.append("\n}");
			return new CallableFlatteningResult(mainBodyOutput.toString(), "");
		}

		List<SolidityModifier> mods = new LinkedList<>();
		modCtxs.forEach(modCtx -> {
			CallableOverloadResolutionResult overloadResult = resolveModifierCall(modCtx);
			if (overloadResult.callable == null) {
				error("Could not resolve modifier call to " + modCtx.identifier());
			}
			SolidityModifier mod = (SolidityModifier)(overloadResult.callable);
			mods.add(mod);
		});

		// An "inlining" flattening is made if two conditions are true:
		//   1) None of the modifiers take any parameters, and
		//   2) None of the modifiers contain any return statements.
		// In this case, the body of each invoked modifier is inlined into the main function body.
		// There are two versions of the inlining flattening:
		// One where the main callable gets inlined as well, and one where it gets its own method, and calls are made
		// to it in place of '_;' statements in the last invoked modifier.
		// The former is chosen if the callable contains no return statements.
		// Otherwise, a more "complicated"/general flattening is created, where both the modifiers and the callable
		// gets their own methods and call each other in place of '_;' statements.
		boolean createInliningFlattening = true;
		for (SolidityModifier mod : mods) {
			if (mod.params != null && !mod.params.isEmpty() || mod.hasReturnStatement()) {
				createInliningFlattening = false;
				break;
			}
		}
		CallableFlatteningResult result;
		if (createInliningFlattening) {
			boolean inlineMainCallable = !callable.hasReturnStatement();
			ModifierFlatteningMode inliningMode = inlineMainCallable ?
					ModifierFlatteningMode.INLINE_MODS_INLINE_FUNCTION : ModifierFlatteningMode.INLINE_MODS_CALL_FUNCTION;
			result = flattenCallableWithModInlining(
					callable,
					braceFreeCallableBodyOutput,
					parentConstructorCallsOutput,
					mods,
					inliningMode
			);
		} else {
			result = flattenCallableWithModCalling(
					callable,
					braceFreeCallableBodyOutput,
					parentConstructorCallsOutput,
					mods,
					modCtxs
			);
		}
		mainBodyOutput.append(result.mainBodyOutput + "\n}\n");
		return new CallableFlatteningResult(mainBodyOutput.toString(), result.externalMethodsOutput);
	}

	/**
	 * Perform an "inlining" flattening, where the bodies of the modifiers are effectively inlined into the main callable.
	 * There are two versions: one where the function body itself is also inlined, and one where it isn't, meaning
	 * that a call to an additional method created is made instead, in place of the _; statements in the last modifier.
	 * @param callable The function/constructor to flatten.
	 * @param braceFreeCallableBodyOutput The output for the main callable body, without the outer braces.
	 * @param parentConstructorCallsOutput The output for the parent constructor calls, as it should be part of the
	 *                                     main function body.
	 * @param mods The modifiers which the function/constructor invoke.
	 * @param mode Which type of "inlining" flattening to perform.
	 * @return The Java output for the flattened method/constructor body, as well as Java output for potential
	 * external methods that were created.
	 */
	private CallableFlatteningResult flattenCallableWithModInlining(SolidityCallable callable,
																	String braceFreeCallableBodyOutput,
																	String parentConstructorCallsOutput,
																	List<SolidityModifier> mods,
																	ModifierFlatteningMode mode)
	{
		if (mode != ModifierFlatteningMode.INLINE_MODS_CALL_FUNCTION &&
				mode != ModifierFlatteningMode.INLINE_MODS_INLINE_FUNCTION)
		{
			error("Invalid modifier flattening mode supplied to function 'flattenCallableWithModInlining'");
		}
		ModifierFlattening.currentModPos = -1;
		ModifierFlattening.currentModList = mods;
		ModifierFlattening.mode = mode;
		ModifierFlattening.mainCallable = callable;
		ModifierFlattening.braceFreeMainCallableBodyOutput = braceFreeCallableBodyOutput;
		ModifierFlattening.parentConstructorCallsOutput = parentConstructorCallsOutput;
		ModifierFlattening.isActive = true;
		String mainBodyOutput = ModifierFlattening.parentConstructorCallsOutput;
		mainBodyOutput += inliningFlatteningGetNextModifierOutput();
		ModifierFlattening.isActive = false;
		CallableFlatteningResult result = new CallableFlatteningResult();
		result.mainBodyOutput = mainBodyOutput;
		if (mode == ModifierFlatteningMode.INLINE_MODS_CALL_FUNCTION) {
			// Create an additional private Java method, corresponding to the modifier-free callable.
			StringBuilder externalOutput = new StringBuilder("private ");
			externalOutput.append(callable instanceof SolidityFunction ? solidityToJavaType(callable.returnType) : "void");
			externalOutput.append(" ");
			externalOutput.append(ModifierFlattening.mainCallable.getModFreeDisplayName(currentContract));
			externalOutput.append(callable.buildParamListWithParen());
			externalOutput.append("{\n");
			// Declare return variables at the top of the function body, and return at the end.
			// This may produce a Java program that does not compile (unreachable code), but we don't care.
			boolean declareReturnVars = ModifierFlattening.mainCallable instanceof SolidityFunction;
			if (declareReturnVars) {
				externalOutput.append(((SolidityFunction)(ModifierFlattening.mainCallable)).declareFunctionReturnVars());
			}
			externalOutput.append(ModifierFlattening.braceFreeMainCallableBodyOutput);
			if (declareReturnVars) {
				externalOutput.append(((SolidityFunction)(ModifierFlattening.mainCallable)).makeFunctionReturnStmnt());
			}
			externalOutput.append("\n}");
			result.externalMethodsOutput = externalOutput.toString();
		} else {
			result.externalMethodsOutput = "";
		}
		return result;
	}

	/**
	 * During the "inlining" modifier flattening process, when a _; statement is encountered in a modifier body,
	 * call this function to get the output of the next modifier in the modifier invocation list (after which it is inlined).
	 * @return The output of the next modifier in the modifier invocation list, or, the function/constructor itself,
	 * if we are currently visiting the last modifier in the list.
	 */
	private String inliningFlatteningGetNextModifierOutput() {
		StringBuilder output = new StringBuilder();
		++ModifierFlattening.currentModPos;
		if (ModifierFlattening.currentModPos == ModifierFlattening.currentModList.size()) {
			// Depending on the mode, either inline the function/constructor body, or make a call to it.
			switch (ModifierFlattening.mode) {
				case INLINE_MODS_INLINE_FUNCTION ->
						output.append(ModifierFlattening.braceFreeMainCallableBodyOutput);
				case INLINE_MODS_CALL_FUNCTION -> {
					if (ModifierFlattening.mainCallable instanceof SolidityFunction &&
							!ModifierFlattening.mainCallable.returnType.equals("void"))
					{
						output.append(((SolidityFunction)ModifierFlattening.mainCallable).makeReturnVarAssignment());
					}
					output.append(ModifierFlattening.mainCallable.getModFreeDisplayName(currentContract));
					output.append(ModifierFlattening.mainCallable.buildArgListWithParen());
					output.append(";");
				}
				default -> error("Unrecognized modifier flattening mode encountered.");
			}

		} else {
			SolidityModifier currentMod = ModifierFlattening.currentModList.get(ModifierFlattening.currentModPos);

			// At the start of the flattened body, declare function return variables, if any.
			boolean declareReturnVarsAndReturnStmnt = ModifierFlattening.currentModPos == 0 &&
					ModifierFlattening.mainCallable instanceof SolidityFunction;
			if (declareReturnVarsAndReturnStmnt) {
				output.append(((SolidityFunction)ModifierFlattening.mainCallable).declareFunctionReturnVars());
			}
			// Visit the body
			output.append(removeOuterBracesFromCallableBodyOutput(currentMod.visitBody()));
			// At the end, return, unless return type is void.
			if (declareReturnVarsAndReturnStmnt) {
				output.append(((SolidityFunction)ModifierFlattening.mainCallable).makeFunctionReturnStmnt());
			}
		}
		--ModifierFlattening.currentModPos;
		return output.toString();
	}

	/**
	 * Perform a "general" flattening, where the bodies of the modifiers are not inlined into the main callable,
	 * but rather, where each invoked modifier gets its own method, containing the body of the modifier, where each _;
	 * has been replaced with a call to the next modifier in the modifier invocation list.
	 * @param callable The function/constructor to flatten.
	 * @param braceFreeCallableBodyOutput The output for the main callable body, without the outer braces.
	 * @param parentConstructorCallsOutput The output for the parent constructor calls, as it should be part of the
	 *                                     main function body.
	 * @param mods The modifiers which the function/constructor invoke.
	 * @param modInvCtxs Contexts for the invoked modifiers (not parent constructors).
	 * @return The Java output for the flattened method/constructor body, as well as Java output for external methods
	 * that were created.
	 */
	private CallableFlatteningResult flattenCallableWithModCalling(SolidityCallable callable,
																   String braceFreeCallableBodyOutput,
																   String parentConstructorCallsOutput,
																   List<SolidityModifier> mods,
																   List<SolidityParser.ModifierInvocationContext> modInvCtxs)
	{
		if (mods.size() != modInvCtxs.size()) {
			error("Modifier list and modifier invocation lists must be of the same size in function flattenCallableGeneral()");
		}

		ModifierFlattening.isActive = true;
		ModifierFlattening.mode = ModifierFlatteningMode.CALL_MODS_CALL_FUNCTION;
		ModifierFlattening.mainCallable = callable;
		ModifierFlattening.currentModList = mods;
		ModifierFlattening.braceFreeMainCallableBodyOutput = braceFreeCallableBodyOutput;
		ModifierFlattening.parentConstructorCallsOutput = parentConstructorCallsOutput;

		HashMap<SolidityModifier, Integer> numberOfOccurrences = new HashMap<>();
		HashMap<SolidityModifier, Integer> numberOfTimesVisited = new HashMap<>();
		mods.forEach(mod -> {
			numberOfOccurrences.merge(mod, 1, Integer::sum); // Add 1 to the count, or if null, make it 1.
			numberOfTimesVisited.putIfAbsent(mod, 0); // Start with 0 initially; below, we do the actual "visiting".
		});

		// output in the form of functions created in addition to the "original"/base function, i.e.,
		// the one that is actually called from outside the contract.
		StringBuilder externalOutput = new StringBuilder();

		// Create the function for the original function/constructor without any mods.
		String returnType = null;
		if (callable instanceof SolidityConstructor) {
			returnType = "void";
		} else if (callable instanceof SolidityFunction) {
			returnType = solidityToJavaType(callable.returnType);
		} else {
			error("Illegitimate SolidityCallable type given to flattenCallableGeneral().");
		}
		externalOutput.append("private " + returnType + " " + callable.getModFreeDisplayName(currentContract));
		externalOutput.append(callable.buildParamListWithParen());
		externalOutput.append("{\n");
		// Declare return variables at the top of the function body, and return at the end.
		// This may produce a Java program that does not compile (unreachable code), but we don't care.
		boolean declareReturnVars = ModifierFlattening.mainCallable instanceof SolidityFunction;
		if (declareReturnVars) {
			externalOutput.append(((SolidityFunction)(ModifierFlattening.mainCallable)).declareFunctionReturnVars());
		}
		externalOutput.append(braceFreeCallableBodyOutput);
		if (declareReturnVars) {
			externalOutput.append(((SolidityFunction)(ModifierFlattening.mainCallable)).makeFunctionReturnStmnt());
		}
		externalOutput.append("\n}\n\n");

		// For each modifier in the list, create a new Java method with the same name, but prefixed with the
		// callable name. If a modifier occurs multiple times, we create one function per modifier occurrence, since
		// whatever '_;' will be replaced with depends on where in the modifier list the modifier is called.
		// First, find what '_;' should actually be replaced with, as well as return statements.
		if (callable instanceof SolidityFunction && !callable.returnType.equals("void")) {
			modifierReturnStmntReplacement = "return " + defaultReturnVariableName + ";";
		} else {
			modifierReturnStmntReplacement = "return;";
		}

		// Save the previous owner and then restore it after all modifiers have been visited.
		// This is because we need to set the owner contract equal to the owner of the modifier when we visit it.
		SolidityContract prevOwnerContract = currentOwnerContract;

		int modIndex = -1;
		for (SolidityModifier mod : mods) {
			modIndex++;
			boolean isTheLastModifier = modIndex == mods.size() - 1;

			currentOwnerContract = contracts.get(mod.ownerName);
			varStack.resetToContractScope();

			structureStack.push(ContractStructure.CALLABLE_HEADER);

			// Find what the underscore replacement should be. When the modifier block is visited and
			// an '_;' is encountered (see visitTerminal()), the replacement takes place.
			StringBuilder underscoreReplacement = new StringBuilder();
			if (callable instanceof SolidityFunction && !returnType.equals("void")) {
				underscoreReplacement.append(defaultReturnVariableName + " = ");
			}
			if (isTheLastModifier) {
				underscoreReplacement.append(callable.getModFreeDisplayName(currentContract) + "(msg,");
				callable.params.forEach(param -> underscoreReplacement.append(
						ModifierFlattening.getDisplayNameOfCallableParamInModifier(param.name) + ","));
				underscoreReplacement.deleteCharAt(underscoreReplacement.length() - 1);
			} else {
				SolidityModifier nextMod = mods.get(modIndex + 1);
				SolidityParser.ModifierInvocationContext nextModCtx = modInvCtxs.get(modIndex + 1);
				String nextModShownName = nextMod.getDisplayName(currentContract, callable,
						numberOfTimesVisited.get(nextMod) + 1, numberOfOccurrences.get(nextMod));
				underscoreReplacement.append(nextModShownName);
				underscoreReplacement.append("(msg,");
				if (nextModCtx.expressionList() != null && !nextModCtx.expressionList().expression().isEmpty()) {
					structureStack.push(ContractStructure.MODIFIER_INVOCATION_FLATTENING);
					for (SolidityParser.ExpressionContext exprCtx : nextModCtx.expressionList().expression()) {
						underscoreReplacement.append(visit(exprCtx) + ",");
					}
					structureStack.pop();
				}
				callable.params.forEach(param -> underscoreReplacement.append(
						"__" + callable.name + "__" + param.name + ","));
				underscoreReplacement.deleteCharAt(underscoreReplacement.length() - 1);
			}
			underscoreReplacement.append(");");

			modifierUnderscoreReplacement = underscoreReplacement.toString();

			// Add to the output a method for the modifier.
			externalOutput.append("private ");
			if (callable instanceof SolidityFunction) {
				externalOutput.append(solidityToJavaType(callable.returnType) + " ");
			} else {
				externalOutput.append("void ");
			}
			String shownModifierName = mod.getDisplayName(currentContract, callable,
					numberOfTimesVisited.get(mod), numberOfOccurrences.get(mod));
			externalOutput.append(shownModifierName);
			externalOutput.append('(');
			externalOutput.append(mod.buildParamList());
			externalOutput.append(',');
			callable.params.forEach(param ->
					externalOutput.append(solidityToJavaType(param.typename) + " " +
							ModifierFlattening.getDisplayNameOfCallableParamInModifier(param.name) + ","));
			externalOutput.deleteCharAt(externalOutput.length() - 1);
			externalOutput.append("){\n");

			structureStack.pop();

			boolean declareModReturnVar = callable instanceof SolidityFunction && !callable.returnType.equals("void");

			if (declareModReturnVar) {
				externalOutput.append(solidityToJavaType(callable.returnType) + " " +
						defaultReturnVariableName + " = " + defaultValueOfType(callable.returnType) + ";");
			}

			externalOutput.append(removeOuterBracesFromCallableBodyOutput(mod.visitBody()));
			externalOutput.append('\n');

			if (declareModReturnVar) {
				externalOutput.append("return " + defaultReturnVariableName + ";\n");
			}

			externalOutput.append("}\n\n");

			Integer numTimesVisited = numberOfTimesVisited.get(mod);
			numberOfTimesVisited.put(mod, numTimesVisited + 1);
		}
		currentOwnerContract = prevOwnerContract;

		// Create the output for the function that will be seen from outside the contract
		StringBuilder bodyOutput = new StringBuilder();
		// Call parent constructors, then the first modifier
		bodyOutput.append(ModifierFlattening.parentConstructorCallsOutput);
		if (callable instanceof SolidityFunction && !callable.returnType.equals("void")) {
			bodyOutput.append("return ");
		}
		SolidityModifier firstMod = mods.get(0);
		SolidityParser.ModifierInvocationContext firstModCtx = modInvCtxs.get(0);
		String shownModName = firstMod.getDisplayName(currentContract, callable, 0, numberOfOccurrences.get(firstMod));
		bodyOutput.append(shownModName);
		bodyOutput.append("(msg,");
		if (firstModCtx.expressionList() != null && !firstModCtx.expressionList().expression().isEmpty()) {
			firstModCtx.expressionList().expression().forEach(expr -> bodyOutput.append(visit(expr) + ","));
		}
		callable.params.forEach(param -> bodyOutput.append(param.name + ","));
		bodyOutput.deleteCharAt(bodyOutput.length() - 1);
		bodyOutput.append(");");

		ModifierFlattening.isActive = false;

		return new CallableFlatteningResult(bodyOutput.toString(), externalOutput.toString());
	}

	// Generated from key.core/src/main/antlr/de/uka/ilkd/key/parser/Solidity.g4 by ANTLR 4.7.1
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
		 * yet, we know that the contract exists (and all of its functions, fields, etc.). */
		SolidityTranslationPreVisitor preVisitor = new SolidityTranslationPreVisitor();
		this.contracts = preVisitor.visit(ctx);
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

		// Create an interface + class (only interface is contract is an interface)
		// from the contract and visit each of its children.
		// The interface contains only function declarations and enum and struct definitions.
		final StringBuilder classOutput = new StringBuilder();
		interfaceOutput = new StringBuilder();

		interfaceOutput.append("interface " + contractName);
		if (contract.inheritanceList.size() > 0) {
			interfaceOutput.append(" extends");
			contract.inheritanceList.forEach(c -> interfaceOutput.append(" " + c + ","));
			interfaceOutput.deleteCharAt(interfaceOutput.length()-1);
		}
		interfaceOutput.append(" {\n");

		if (contract.type == ContractType.CONTRACT) {
			if (contract.isAbstract) {
				classOutput.append("abstract ");
			}
			classOutput.append("class " + contract.getDisplayName() +
					" extends Address implements " + contractName + " {\n");
			ctx.contractPart().stream().forEach(part -> classOutput.append(visit(part) + '\n'));
		} else if (contract.type == ContractType.INTERFACE) {
			// interfaceOutput is appended to manually when we see a func decl, struct def, etc.
			ctx.contractPart().stream().forEach(part -> visit(part));
		} else if (contract.type == ContractType.LIBRARY) {
			classOutput.append("class " + contractName + " {\n");
			ctx.contractPart().stream().forEach(part -> classOutput.append(visit(part) + '\n'));
		} else {
			error("Unrecognized contract type for contract " + contractName + " encountered.");
		}

		/* Import all inherited functions, fields, modifiers, and constructors from the contract's parents.
		   This is not done for interfaces or libraries.
		   Inherited functions and modifiers are renamed, but only if they are overridden.
		   Fields are only renamed if they are private. Super calls are also replaced with calls to explicit functions.
		 */
		if (contract.type == ContractType.CONTRACT) {
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

				// Import fields
				parent.fields.forEach(field -> classOutput.append(visit(field.ctx) + '\n'));

				// Import functions
				parent.functions.forEach(fun -> {
					if (!fun.isAbstract) { // Do not import abstract functions.
						classOutput.append(visit(fun.ctx) + '\n');
					}
				});

				// Import constructors (as functions). Each base class can have at most one constructor.
				if (parent.hasNonDefaultConstructor())
					classOutput.append(visit(parent.constructor.ctx) + '\n');
			}
		}

		interfaceOutput.append("}\n");
		// Contract => class + interface. Interface => interface. Library => class.
		if (contract.type != ContractType.LIBRARY) {
			output.append(interfaceOutput);
		}
		if (contract.type != ContractType.INTERFACE) {
			classOutput.append("}\n");
			output.append(classOutput);
		}

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

		StringBuilder output = new StringBuilder();

		output.append(switch (field.visibility) {
			case PUBLIC -> "public";
			case PRIVATE -> "private";
			// The default visibility is "internal", roughly corresponding to java's "protected".
			default -> "protected";
		});
		if (field.isConstant) {
			output.append(" final");
		}

		String displayName = field.getDisplayName(currentContract);
		String shownTypename = solidityToJavaType(field.typename);
		if (nameIsAContract(field.typename))
			shownTypename = contracts.get(field.typename).getDisplayName();

		output.append(" " + shownTypename + " " + displayName);

		structureStack.pop();
		structureStack.push(ContractStructure.FIELD_DECL_RIGHT);

		if (ctx.expression() != null && !ctx.expression().isEmpty()) {
			output.append(" = " + visit(ctx.expression()));
		}
		output.append(";");

		structureStack.pop();

		return output.toString();
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitUsingForDeclaration(SolidityParser.UsingForDeclarationContext ctx) { return ""; }

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
		interfaceOutput.append(output);
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
		if (ctx.block() == null) {
			error("Constructor must be defined if declared. See contract " + currentContract.name + ".");
		}

		SolidityConstructor constructor = currentOwnerContract.constructor;

		structureStack.push(ContractStructure.CALLABLE_HEADER);

		String visibility;
		String returnType;
		if (currentlyVisitingInheritedMember()) {
			// "Inherit" the constructor by constructing a new private function representing its body and modifiers.
			visibility = "private";
			returnType = "void";
		} else {
			visibility = "public"; // Note: constructors in Solidity are always public (as of now)
			returnType = "";
		}

		String parameters = constructor.buildParamListWithParen();
		String headerOutput = visibility + " " + returnType + " " +
				constructor.getDisplayName(currentContract) + parameters;

		structureStack.pop();

		// Even if they are not invoked explicitly, all constructors of the current contract's C3 linearization
		//  should be invoked. If a given parent constructor is parameter-free, and it is "invoked" twice
		// (e.g., the child constructor invokes it twice, or another parent constructor invokes it),
		// then the constructor will be invoked only once. If a given parent constructor has parameters
		// and is invoked twice (e.g. this constructor calls it with argument int:0, and another contract constructor
		// that is also called calls it with argument int:1, the Solidity compiler will not allow this! This is true
		// even if the supplied arguments are all equal.
		//
		// Our solution regarding the output Java constructor and class (inheritance flattening):
		// The beginning of the flattened contract's constructor shall contain calls to all parent constructors, with
		// the arguments supplied. The parent constructors are modelled as private methods. When visiting the
		// parent constructors as part of the flattening process, we ignore all parent constructor invocations,
		// since these will have already been invoked from this constructor. However, we still handle the
		// modifier invocations.

		StringBuilder braceFreeBodyOutput = new StringBuilder(removeOuterBracesFromCallableBodyOutput(constructor.visitBody()));

		if (currentlyVisitingInheritedMember() && ctx.modifierList() == null) {
			return headerOutput + "{\n" + braceFreeBodyOutput + "\n}\n";
		} else {
			structureStack.push(ContractStructure.CALLABLE_HEADER);

			// A constructor "modifier" may be a call to a parent constructor, or to an actual modifier. Collect those.
			// As mentioned above, if we are currently visiting an inherited constructor, only collect modifiers.
			List<SolidityParser.ModifierInvocationContext> constructorCalls = new LinkedList<>();
			List<SolidityParser.ModifierInvocationContext> modCalls = new LinkedList<>();
			if (ctx.modifierList() != null) {
				for (SolidityParser.ModifierInvocationContext mod : ctx.modifierList().modifierInvocation()) {
					String identifier = visit(mod.identifier());
					// Check whether the identifier is a modifier or a constructor
					int linearizationPos = currentOwnerContract.c3Linearization.indexOf(identifier);
					boolean isConstructorInvocation = linearizationPos != -1;
					if (!isConstructorInvocation) {
						modCalls.add(mod);
					} else if (!currentlyVisitingInheritedMember()) {
						constructorCalls.add(mod);
					}
				}
			}
			structureStack.pop();

			StringBuilder parentConstructorCallsOutput = new StringBuilder();

			if (!currentlyVisitingInheritedMember()) {
				// Collect all constructors invoked by the parent constructors
				for (String parentName : currentContract.c3Linearization) {
					SolidityConstructor parentConstructor = contracts.get(parentName).constructor;
					List<SolidityParser.ModifierInvocationContext> parentConstructorInvocations =
							parentConstructor.getAllParentConstructorInvocations();
					// Merge the two lists
					constructorCalls = Stream.of(constructorCalls, parentConstructorInvocations)
							.flatMap(Collection::stream)
							.collect(Collectors.toList());
				}

				// Go through all the parents of the current contract and locate the corresponding constructor invocations.
				// Add to the constructor body output an invocation of the constructors with the found arguments.
				// If an invocation can not be found, simply add "CImpl(msg);", where C is the name of the parent, to the output,
				// if the constructor of C is parameter-free. Otherwise, throw an error.
				for (String parentName : currentContract.c3Linearization) {
					if (parentName.equals(currentContract.name))
						continue;
					SolidityContract parent = contracts.get(parentName);
					// Locate the invocation of the parent constructor.
					// If there are two invocations, this is undefined behaviour (Solidity program would not compile)
					boolean invFound = false;
					for (SolidityParser.ModifierInvocationContext invCtx : constructorCalls) {
						if (invCtx.identifier().getText().equals(parentName)) {
							parentConstructorCallsOutput.append(parent.getDisplayName() + "(msg,");
							if (invCtx.expressionList() != null && !invCtx.expressionList().expression().isEmpty()) {
								invCtx.expressionList().expression().forEach(expr ->
										parentConstructorCallsOutput.append(visit(expr) + ','));
							}
							parentConstructorCallsOutput.deleteCharAt(parentConstructorCallsOutput.length() - 1);
							parentConstructorCallsOutput.append(");\n");
							invFound = true;
							break;
						}
					}
					if (!invFound) {
						if (contracts.get(parentName).constructor.params.isEmpty()) {
							parentConstructorCallsOutput.append(parent.getDisplayName() + "(msg);\n");
						} else {
							error("The constructor for contract " + currentOwnerContract.name +
									" does not invoke parent constructor " + parent.name);
						}
					}
				}
			}

			CallableFlatteningResult result = createFlattenedCallable(
					constructor,
					braceFreeBodyOutput.toString(),
					parentConstructorCallsOutput.toString(),
					modCalls
			);
			return headerOutput + result.mainBodyOutput + result.externalMethodsOutput;
		}
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
		structureStack.push(ContractStructure.CALLABLE_HEADER);

		String funName = ctx.identifier().getText();
		LinkedList<String> argTypes = new LinkedList<>();
		ctx.parameterList().parameter().forEach(parameter -> argTypes.add(visit(parameter.typeName())));
		SolidityFunction function = currentOwnerContract.getFunction(funName, argTypes, false, false);
		if (function == null) {
			error("Could not locate function " + funName + " in contract " + currentOwnerContract.name);
		}

		String visibility;
		if (function.isLibraryFunction) {
			// Library functions cannot be private it seems, and if it is internal, it can still be called from anywhere.
			visibility = "public";
		} else {
			visibility = switch (function.visibility) {
				case PUBLIC, EXTERNAL -> "public";
				case INTERNAL -> "protected";
				case PRIVATE -> "private";
				default -> error("Unrecognized visibility.");
			};
		}

		String shownFunName = function.getDisplayName(currentContract);
		String parameters = function.buildParamListWithParen();
		String returnType = solidityToJavaType(function.returnType);
		String fctHeader = visibility + (currentContract.type == ContractType.LIBRARY ? " static " : " ") +
				(function.isAbstract ? "abstract " : "") +
				returnType + " " + shownFunName + parameters;

		/* The function declaration is added to an interface accompanying the output class, unless the function was
		   inherited. With the function being abstract, it is added to the class as an abstract method,
		   and only added to the interface if its visibility is either public or package-protected.
		   This is because Java interfaces cannot have private/protected methods.
		 */
		if (!currentlyVisitingInheritedMember() && !function.overrides && visibility.equals("public")) {
			interfaceOutput.append(fctHeader + ";\n");
		}

		structureStack.pop();

		// If the function is abstract or if the contract is an interface,
		// only add its declaration to the interface (done above).
		if (function.isAbstract || currentContract.type == ContractType.INTERFACE) {
			return "";
		} else {
			StringBuilder braceFreeBodyOutput = new StringBuilder(removeOuterBracesFromCallableBodyOutput(function.visitBody()));
			if (ctx.modifierList().modifierInvocation().isEmpty()) {
				// Declare return variables at the top of the function body, and return at the end.
				// This may produce a Java program that does not compile (unreachable code), but we don't care.
				braceFreeBodyOutput.insert(0, "{\n" + function.declareFunctionReturnVars());
				braceFreeBodyOutput.append(function.makeFunctionReturnStmnt() + "\n}");
				return fctHeader + " " + braceFreeBodyOutput;
			} else {
				CallableFlatteningResult result = createFlattenedCallable(
						function,
						braceFreeBodyOutput.toString(),
						"", // parent constructor calls (only applicable for constructors)
						ctx.modifierList().modifierInvocation()
				);
				return fctHeader + result.mainBodyOutput + result.externalMethodsOutput;
			}
		}
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

		String shownTypename = solidityToJavaType(typename);
		if (nameIsAContract(typename)) // If it is a contract type
			shownTypename = contracts.get(typename).getDisplayName();

		SolidityVariable var = new SolidityVariable(identifier, typename);
		varStack.pushVar(var);
		return shownTypename + " " + identifier;
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitTypeName(SolidityParser.TypeNameContext ctx) {
		return ctx.getText();
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
		// If we are in a modifier, invoked by a non-void function, replace "return;" with "return __returnVal;"
		if (ModifierFlattening.isActive && structureStack.contains(ContractStructure.MODIFIER_BODY)) {
			return modifierReturnStmntReplacement;
		}
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
		return ctx.getText();
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
		return (ctx.unop.equals(ctx.INC()) ? "++" : "--") + visit(ctx.expression());
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
		return visit(ctx.expression()) + (ctx.unop.equals(ctx.INC()) ? "++" : "--");
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
		String displayedName = fctName;
		SolidityCallable resolvedCallable = null;
		FunctionCallReferenceType resolvedReferenceType = null;
		boolean functionIsAGetter = false; // a function call can "disguise" itself as a call to a getter for a field
		// If the function name is reserved, we output it as in (no renaming).
		Optional<String> reservedFunctionType = getReservedFunctionReturnTypeContractContext(fctName, currentOwnerContract, true);
		if (reservedFunctionType.isEmpty()) {
			CallableOverloadResolutionResult overload = resolveFunctionCall(ctx);
			resolvedCallable = overload.callable;
			functionIsAGetter = overload.field != null;
			displayedName = overload.displayedName;
			resolvedReferenceType = overload.referenceType;
		}

		if (functionIsAGetter) {
			return displayedName;
		}

		StringBuffer arguments;
		// Do not append the "msg" argument if the call is made to a built-in Solidity function.
		boolean skipMsgArg = reservedFunctionType.isPresent();

		// TODO: explain what "require2" and "require3" is.
		String beginArg;
		if (displayedName.equals("require2")) {
			beginArg = "(int)sender != 0,";
		} else if (displayedName.equals("require3")) {
			beginArg = "(int)recipient != 0,";
		} else if (skipMsgArg) {
			beginArg = "";
		} else {
			beginArg = "msg,";
		}
		arguments = new StringBuffer(beginArg);

		// If the resolved function is a library function, and it was referenced from an object
		//  (i.e., using the Using For construct: obj.foo(...), and not LibName.foo(...)),
		//  turn the function call into LibName.foo(obj, ...). Also, we keep internal library function calls the same.
		boolean addThisArg = resolvedCallable instanceof SolidityFunction &&
				((SolidityFunction)resolvedCallable).isLibraryFunction &&
				resolvedReferenceType != FunctionCallReferenceType.LIBRARY &&
				currentContract.type != ContractType.LIBRARY;
		if (addThisArg) {
			String thisArg;
			if (resolvedReferenceType == FunctionCallReferenceType.OBJECT) {
				String obj = fctName.substring(0, fctName.indexOf("."));
				SolidityVariable var = varStack.getVariableFromIdentifier(obj);
				thisArg = var.getDisplayName(currentContract);
			} else {
				thisArg = "this";
			}
			// append the object as an argument to the library function.
			arguments.append(thisArg + ",");
		}

		if (ctx.functionCallArguments() != null && !ctx.functionCallArguments().isEmpty()) {
			if (ctx.functionCallArguments().expressionList()!= null &&
					!ctx.functionCallArguments().expressionList().isEmpty()) {
				ctx.functionCallArguments().expressionList().expression().stream()
						.forEach(elt -> arguments.append(visit(elt)+","));
			}
		}
		if (arguments.length() != 0)
			arguments.deleteCharAt(arguments.length() - 1);

		return displayedName + "(" + arguments + ")";
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
		// If you have more than one dot, say A.B.C.D, this method will still be called only once,
		//  and "expression" will contain "A.B.C", while "identifier" contains "D".

		// TODO: As far as I can see, when the dot expression is also part of a function call, visitDotExpression works
		//  with visitFunctionCallExpression as follows. First, visitDotExpression is called. We return the output.
		//  Then, visitFunctionCall is called, and the output from visitDotExpression is then used as
		//  the input function name (ctx.expression()).
		//  If this is a field getter call, we can simply let resolveFunctionCall() do its job by identifying that it
		//  is a field and rename everything that needs to be renamed. We do not rename anything here, otherwise,
		//  the resolution may not work correctly.
		//  However, if this is not a field getter call, and e.g. just a field access without the (), we need to format
		//  the correct output here, and e.g. rename what is front of the dot if it refers to an object that has
		//  been inherited.
		//  However, from here, we have no way of knowing whether this expression is part of a function call or not.
		//  >>> For now: the assumption is that for field accesses with a qualifier (where a dot is involved),
		//  we always use the getter (i.e., the '()'), i.e., we don't access the field "raw" (e.g. C.field).
		//  This is not needed for field access on 'msg' or elementary types.
		String beforeDot = ctx.expression().getText();
		String afterDot = ctx.identifier().getText();
		return beforeDot + "." + afterDot;
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitUnaryAdditiveExpression(SolidityParser.UnaryAdditiveExpressionContext ctx) {
		return (ctx.unop == ctx.MINUS() ? "-" : "") + visitChildren(ctx);
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

		if (!structureStack.isEmpty() && structureStack.peek() == ContractStructure.MODIFIER_INVOCATION_FLATTENING) {
			// We are now performing modifier flattening, and are about to insert a call to another modifier.
			// We are visiting the argument list of the next modifier. These have nothing to do with the current modifier,
			// however, they cannot use the arguments of the main function/constructor. Thus, if we see an identifier,
			// it must be one of the function/constructor parameters. We rename it so that it doesn't clash
			// with the modifier parameters.
			return ModifierFlattening.getDisplayNameOfCallableParamInModifier(identifier);
		}

		SolidityVariable var = varStack.getVariableFromIdentifier(identifier);
		if (var == null) {
			// The identifier is not of a variable or field. If it is a function call, resolveFunctionCall takes care of renaming.
			return identifier;
		}
		/* If the identifier is of a private field that has been inherited, then this should be renamed if
		   a subcontract has defined a field with the same identifier.
		   The name should not be mangled if resides in a definition where a new name is introduced, e.g.,
		   the header of a function/modifier/constructor definition, or on the left side of the '=' in a
		   variable declaration.
		 */
		if (var instanceof SolidityField) {
			return switch (structureStack.peek()) {
				case CALLABLE_INVOCATION, CONSTRUCTOR_BODY, FUNCTION_BODY, MODIFIER_BODY, FIELD_DECL_RIGHT ->
						var.getDisplayName(currentContract);
				default -> identifier;
			};
		}
		return identifier;
	}

	@Override public String visitTerminal(TerminalNode n) {
		if (structureStack.contains(ContractStructure.MODIFIER_BODY)) {
			// We are now visiting the _; statement found inside of modifiers.
			if (ModifierFlattening.mode == ModifierFlatteningMode.INLINE_MODS_CALL_FUNCTION ||
					ModifierFlattening.mode == ModifierFlatteningMode.INLINE_MODS_INLINE_FUNCTION)
			{
				return inliningFlatteningGetNextModifierOutput();
			} else {
				return modifierUnderscoreReplacement;
			}
		}
		return "";
	}

	public String getOutput() {
		return output.toString();
	}

	/* This visitor is used to collect all the contracts and their functions/fields/modifiers/constructors that
	   are within the input file, before the bodies of these are actually visited to produce the Java text output.
	   This is so that, e.g., if a function calls another function that is defined after the former function,
	   that function can know that the latter function exists.
	   In addition, we also construct C3 linearizations of the inheritance hierarchy within the input file.
	 */
	private class SolidityTranslationPreVisitor extends SolidityBaseVisitor<Map<String, SolidityContract>> {
		Map<String, SolidityContract> contracts = new HashMap<>();
		SolidityContract currentContract;
		SolidityCallable currentCallable;

		@Override
		public Map<String, SolidityContract> visitSourceUnit(SolidityParser.SourceUnitContext ctx) {
			ctx.contractDefinition().forEach(contract -> visit(contract));
			return contracts;
		}

		@Override
		public Map<String, SolidityContract> visitContractDefinition(SolidityParser.ContractDefinitionContext ctx) {
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
		public Map<String, SolidityContract> visitFunctionDefinition(SolidityParser.FunctionDefinitionContext ctx) {
			SolidityFunction function = new SolidityFunction();
			currentContract.functions.add(function);
			currentCallable = function;
			String fctName = ctx.identifier() == null ? "fallback" : ctx.identifier().getText();
			function.ctx = ctx;
			function.name = fctName;
			function.ownerName = currentContract.name;

			// TODO: currently, if the function has several return variables,
			//  the function return type is set to the type of the first return variable.
			function.returnType = ctx.getParent() instanceof ConstructorDefinitionContext ? "" : "void";
			function.returnVars = new LinkedList<>();
			if (ctx.returnParameters() != null && !ctx.returnParameters().isEmpty()) {
				function.returnType = ctx.returnParameters().parameterList().parameter(0).typeName().getText();
				ctx.returnParameters().parameterList().parameter().forEach(param -> {
					// Add only named variables. TODO: add unnamed as well?
					if (param.identifier() != null) {
						function.returnVars.add(
								new SolidityVariable(param.identifier().getText(), param.typeName().getText()));
					}
				});
			}

			function.isLibraryFunction = currentContract.type == ContractType.LIBRARY;
			function.isAbstract = ctx.block() == null;
			function.isVirtual = !ctx.modifierList().VirtualKeyword().isEmpty();
			function.overrides = !ctx.modifierList().OverrideKeyword().isEmpty();
			ctx.modifierList().stateMutability().forEach(term -> {
				if (term.PayableKeyword() != null) {
					function.isPayable = true;
				} else if (term.PureKeyword() != null) {
					function.isPure = true;
				} else if (term.ViewKeyword() != null) {
					function.isView = true;
				}
			});
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
		public Map<String, SolidityContract> visitModifierDefinition(SolidityParser.ModifierDefinitionContext ctx) {
			SolidityModifier modifier = new SolidityModifier();
			currentContract.modifiers.add(modifier);
			currentCallable = modifier;
			modifier.name = ctx.identifier() == null ? "fallback" : ctx.identifier().getText();
			modifier.ctx = ctx;
			modifier.ownerName = currentContract.name;
			if (ctx.parameterList() != null && !ctx.parameterList().parameter().isEmpty()) {
				ctx.parameterList().parameter().forEach(param -> visit(param));
			}
			// Note: modifiers' visibility cannot be specified (they are always private).
			return contracts;
		}

		@Override
		public Map<String, SolidityContract> visitStateVariableDeclaration(SolidityParser.StateVariableDeclarationContext ctx) {
			SolidityField field = new SolidityField(ctx.identifier().getText(), ctx.typeName().getText());
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
		public Map<String, SolidityContract> visitConstructorDefinition(SolidityParser.ConstructorDefinitionContext ctx) {
			if (currentContract.hasNonDefaultConstructor())
				error("Cannot define more than one constructor for contract " + currentContract.name);
			SolidityConstructor constructor = new SolidityConstructor();
			currentCallable = currentContract.constructor = constructor;
			constructor.ctx = ctx;
			constructor.name = constructor.ownerName = constructor.returnType = currentContract.name;
			if (ctx.parameterList() != null && !ctx.parameterList().parameter().isEmpty()) {
				ctx.parameterList().parameter().forEach(param -> visit(param));
			}
			return contracts;
		}

		@Override
		public Map<String, SolidityContract> visitParameter(SolidityParser.ParameterContext ctx) {
			// Note: in Solidity, unnamed function parameters allowed.
			// For now, we disallow such parameters, for otherwise, the output Java program may become nonsensical.
			if (ctx.identifier() == null) {
				error("SolidiKeY disallows unnamed parameters. See callable '" + currentCallable.name + "';");
			}
			SolidityVariable var = new SolidityVariable(ctx.identifier().getText(), ctx.typeName().getText());
			currentCallable.params.add(var);
			return contracts;
		}

		@Override
		public Map<String, SolidityContract> visitEnumDefinition(SolidityParser.EnumDefinitionContext ctx) {
			currentContract.enums.add(
					new SolidityEnum(ctx.identifier().getText(), currentContract.name));
			return contracts;
		}

		@Override
		public Map<String, SolidityContract> visitStructDefinition(SolidityParser.StructDefinitionContext ctx) {
			SolidityStruct struct = new SolidityStruct(ctx.identifier().getText(), currentContract.name);
			if (ctx.variableDeclaration() != null) {
				ctx.variableDeclaration().forEach(varCtx ->
						struct.fields.add(new SolidityVariable(varCtx.identifier().getText(), varCtx.typeName().getText())));
			}
			currentContract.structs.add(struct);
			return contracts;
		}

		@Override
		public Map<String, SolidityContract> visitUsingForDeclaration(SolidityParser.UsingForDeclarationContext ctx) {
			// Seemingly, this statement may only appear at contract scope. If it doesn't, the Solidity program
			// would not compile, and we take it as undefined behaviour.
			String lib = ctx.identifier().getText();
			if (ctx.typeName() == null) { // A '*'; means that all contracts/structs in the source file will attach the library functions
				currentContract.globalUsingForLibraries.add(lib);
			} else {
				String type = ctx.typeName().getText();
				if (currentContract.typeLibAttachments.get(type) == null) {
					currentContract.typeLibAttachments.put(type, new LinkedList<>(Collections.singleton(lib)));
				} else {
					currentContract.typeLibAttachments.get(type).add(lib);
				}
			}
			return contracts;
		}

		/**
		 * Constructs the C3 linearization for 'contract', which is a list of contracts that the contract
		 * inherits from, from least derived to most derived, including the contract itself at the end.
		 * In other words, it is a flattening of the contract's inheritance tree structure.
		 * @param contract The contract whose linearization is to be constructed.
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
					if (candidateAppearsOnlyAtEnd(candidate, toMerge)) {
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

		/**
		 * Utility function; check whether 'candidate' appears only at the end of all lists, if it appears at all.
		 * @param candidate The item to check for.
		 * @param lists A list of lists to check.
		 * @return True if 'candidate' appears only at thend of all lists, false otherwise.
		 */
		private boolean candidateAppearsOnlyAtEnd(final String candidate, final LinkedList<LinkedList<String>> lists) {
			for (LinkedList<String> list : lists) {
				int candidatePos = list.indexOf(candidate);
				if (candidatePos != -1 && candidatePos < list.size() - 1) {
					return false;
				}
			}
			return true;
		}
	}

	/**
	 * This visitor is used to get the (Solidity) type of a Solidity expression.
	 * This is used so that proper function overloading can occur when we encounter a function call,
	 * by examining the types of the arguments given.
	 */
	private class SolidityExpressionTypeVisitor extends SolidityBaseVisitor<String> {
		boolean currentlyVisitingUnaryMinus = false;

		@Override public String visitAndExpression(SolidityParser.AndExpressionContext ctx) {
			return "bool";
		}

		@Override public String visitArrayAccessExpression(SolidityParser.ArrayAccessExpressionContext ctx) {
			String arrId = ctx.expression(0).getText();
			return varStack.getTypeofIdentifier(arrId);
		}

		@Override public String visitAssignmentExpression(SolidityParser.AssignmentExpressionContext ctx) {
			return visit(ctx.expression(0));
		}

		@Override public String visitCompExpression(SolidityParser.CompExpressionContext ctx) {
			return "bool";
		}

		@Override public String visitEqualityExpression(SolidityParser.EqualityExpressionContext ctx) {
			return "bool";
		}

		@Override public String visitFunctionCallExpression(SolidityParser.FunctionCallExpressionContext ctx) {
			String fctName = ctx.expression().getText();
			Optional<String> reservedFunctionType = getReservedFunctionReturnTypeContractContext(fctName, currentOwnerContract, true);
			if (reservedFunctionType.isPresent()) {
				return reservedFunctionType.get();
			}
			CallableOverloadResolutionResult result = resolveFunctionCall(ctx);
			if (result.callable != null) {
				return result.callable.returnType;
			} else if (result.field != null) {
				return result.field.typename;
			} else {
				error("Unsuccessful function overload resolution when visiting a function call expression in contract "
						+ currentContract.name);
				return "void";
			}
		}

		@Override public String visitNotExpression(SolidityParser.NotExpressionContext ctx) {
			return "bool";
		}

		@Override public String visitUnaryAdditiveExpression(SolidityParser.UnaryAdditiveExpressionContext ctx) {
			if (ctx.unop == ctx.MINUS())
				currentlyVisitingUnaryMinus = true;
			String result = visitChildren(ctx);
			currentlyVisitingUnaryMinus = false;
			return result;
		}

		@Override public String visitPrimaryExpression(SolidityParser.PrimaryExpressionContext ctx) {
			if (ctx.BooleanLiteral() != null) {
				return "bool";
			} else if (ctx.numberLiteral() != null) {
				if (currentlyVisitingUnaryMinus)
					return "int";
				return "uint";
			} else if (ctx.HexLiteral() != null) {
				return "uint";
			} else if (ctx.StringLiteral() != null) {
				return "string";
			} else if (ctx.identifier() != null) {
				if (ctx.getText().equals("this")) {
					return currentOwnerContract.name;
				}
				String typeName = varStack.getTypeofIdentifier(ctx.getText());
				if (typeName == null) {
					error("Could not find the type of identifier " + ctx.identifier().getText() +
							" in contract " + currentContract.name);
				}
				return typeName;
			} else if (ctx.tupleExpression() != null) {
				// TODO
				error("Tuple expressions not supported.");
				return "";
			} else if (ctx.elementaryTypeNameExpression() != null) {
				// TODO: Unsure what this means
				error("Elementary type name expressions not supported.");
				return "";
			} else {
				error("Unsupported primary expression encountered.");
				return "";
			}
		}

		@Override public String visitOrExpression(SolidityParser.OrExpressionContext ctx) {
			return "bool";
		}

		@Override public String visitTernaryExpression(SolidityParser.TernaryExpressionContext ctx) {
			return visit(ctx.expression(1));
		}

		@Override public String visitDotExpression(SolidityParser.DotExpressionContext ctx) {
			// If you have more than one dot, say "A.B.C.D", this method will still be called only once,
			//  and "expression" will contain "A.B.C", while "identifier" contains "D".

			// If this is part of a function call expression, then visitFunctionCallExpression gets called after this,
			// and whatever type that returns will override whatever type is returned from here.

			String beforeDot = ctx.expression().getText();
			String afterDot = ctx.identifier().getText();
			return lookupTypeForDotExpressionContractContext(beforeDot + "." + afterDot, currentOwnerContract, true);
		}

		// TODO: the below "lookupType" functions could be made more generalized and maintainable

		/**
		 * Get the type of an expression, which may contain any number of dots, as it is used in the given contract.
		 * NOTE: if the expression is a function call, this function will return void (it cannot properly resolve
		 * the type of the function call as it doesn't know the given arguments; this is the job of the method
		 * 'resolveFunctionCall). However, this function is called from visitDotExpression, and if the given dot
		 * expression is also part of a function call expression, the result from visitDotExpression will be discarded,
		 * and only the result from visitFunctionCallExpression is used.
		 * @param exp The expression to evaluate the type of.
		 * @param containingContract The contract in which the expression exists.
		 * @param checkLocalVars Whether to check if the expression or parts of it could be a local variable.
		 *                       If so, the variable scope stack is checked.
		 * @return The Solidity type of the expression, or void, if we came to the conclusion that the expression
		 * must be a function call.
		 */
		private String lookupTypeForDotExpressionContractContext(String exp, SolidityContract containingContract, boolean checkLocalVars) {
			SolidityEnum enum_ = containingContract.lookupEnum(exp);
			if (enum_ != null)
				return enum_.toString();
			SolidityStruct struct = containingContract.lookupStruct(exp);
			if (struct != null)
				return struct.toString();
			int firstDotPos = exp.indexOf(".");
			if (firstDotPos == -1) {
				if (checkLocalVars) {
					SolidityVariable var = varStack.getVariableFromIdentifier(exp);
					if (var != null)
						return var.typename;
				}
				SolidityField field = containingContract.lookupField(exp);
				if (field != null)
					return field.typename;
				SolidityContract contract = contracts.get(exp);
				if (contract != null)
					return contract.name;
				// * If the input Solidity function compiled, the expression must have been a function/constructor call.
				// However, visitFunctionCall is always called after visitDotCall if the dot expression was also part
				// of a function call, and the result of the function call always overrides the result of the
				// dot expression. Hence, it *should* be safe to return void from here.
			} else {
				String beforeFirstDot = exp.substring(0, firstDotPos);
				String afterFirstDot = exp.substring(firstDotPos + 1);
				if (beforeFirstDot.equals("msg")) {
					return lookupTypeForDotExpressionMsgContext(afterFirstDot);
				} else if (nameIsAContract(beforeFirstDot)) {
					return lookupTypeForDotExpressionContractContext(afterFirstDot, contracts.get(beforeFirstDot), false);
				} else {
					if (checkLocalVars) {
						SolidityVariable var = varStack.getVariableFromIdentifier(beforeFirstDot);
						if (var != null) {
							if (nameIsAContract(var.typename)) {
								return lookupTypeForDotExpressionContractContext(afterFirstDot, contracts.get(var.typename), false);
							}
							SolidityStruct struct_ = containingContract.lookupStruct(var.typename);
							if (struct_ != null) {
								return lookupTypeForDotExpressionStructContext(afterFirstDot, struct_);
							}
							return lookupTypeForDotExpressionElementaryTypeContext(afterFirstDot, var.typename);
						}
					}
					SolidityField field = containingContract.lookupField(beforeFirstDot);
					if (field != null) {
						if (nameIsAContract(field.typename)) {
							return lookupTypeForDotExpressionContractContext(afterFirstDot, contracts.get(field.typename), false);
						}
						SolidityStruct struct_ = containingContract.lookupStruct(field.typename);
						if (struct_ != null) {
							return lookupTypeForDotExpressionStructContext(afterFirstDot, struct_);
						}
						return lookupTypeForDotExpressionElementaryTypeContext(afterFirstDot, field.typename);
					}
					if (nameIsAContract(beforeFirstDot))
						return lookupTypeForDotExpressionContractContext(afterFirstDot, contracts.get(beforeFirstDot), false);
					if (beforeFirstDot.equals("this"))
						return lookupTypeForDotExpressionContractContext(afterFirstDot, containingContract, false);
					if (beforeFirstDot.equals("super")) // Only parent functions can be accessed in this way. // See comment *
						return "void";
				}
			}
			return "void";
		}

		/**
		 * Return the Solidity type of the given expression, when in the top-level scope of the given struct.
		 * Example: for s.a.balance, where 's' is a struct instance, and 'a' is a field of that struct of type 'address';
		 * the 'exp' would be 'a.balance', and 'containingStruct' would be the type of 's'.
		 * @param exp The expression, with any number of qualifiers.
		 * @param containingStruct The struct in which the name was referenced (e.g., function call was made)
		 * @return The Solidity type of the expression, or void, if we came to the conclusion that the expression
		 * must be a function call.
		 */
		private String lookupTypeForDotExpressionStructContext(String exp, SolidityStruct containingStruct) {
			int firstDotPos = exp.indexOf(".");
			String beforeFirstDot = firstDotPos == -1 ? exp : exp.substring(0, firstDotPos);
			String afterFirstDot = firstDotPos == -1 ? exp : exp.substring(firstDotPos + 1);
			String type = null;
			for (SolidityVariable var : containingStruct.fields) {
				if (var.name.equals(beforeFirstDot)) {
					type = var.typename;
					break;
				}
			}
			if (type == null) {
				error("Could not find variable " + beforeFirstDot + " in struct " + containingStruct);
			}
			if (firstDotPos == -1) {
				return type;
			}
			if (nameIsAContract(type))
				return lookupTypeForDotExpressionContractContext(afterFirstDot, contracts.get(type), false);
			SolidityContract structOwner = contracts.get(containingStruct.ownerName);
			SolidityStruct struct = structOwner.lookupStruct(type);
			if (struct != null)
				return lookupTypeForDotExpressionStructContext(afterFirstDot, struct);
			SolidityEnum enum_ = structOwner.lookupEnum(type);
			if (enum_ != null)
				return enum_.toString();
			return lookupTypeForDotExpressionElementaryTypeContext(afterFirstDot, type);
		}

		/**
		 * Return the Solidity type of the given expression, when in the top-level scope of the "Message" global variable.
		 * Example: msg.sender.balance; This function would then be called with 'exp' being equal to "sender.balance"
		 * @param exp The expression, with any number of qualifiers.
		 * @return The Solidity type of the expression, or void, if we came to the conclusion that the expression
		 * must be a function call.
		 */
		private String lookupTypeForDotExpressionMsgContext(String exp) {
			int firstDotPos = exp.indexOf(".");
			String beforeFirstDot = firstDotPos == -1 ? exp : exp.substring(0, firstDotPos);
			String afterFirstDot = firstDotPos == -1 ? exp : exp.substring(firstDotPos + 1);
			String msgFieldType = reservedMsgFields.get(beforeFirstDot);
			if (msgFieldType == null) {
				error("Could not find type of expression " + exp + " as part of the global 'msg' variable.");
			}
			if (firstDotPos == -1) {
				return msgFieldType;
			} else {
				return lookupTypeForDotExpressionElementaryTypeContext(afterFirstDot, msgFieldType);
			}
		}

		/**
		 * Return the Solidity type of the given expression, when in the top-level scope of an elementary type.
		 * Example: for a.balance, 'a' is a variable of type 'address'; the 'exp' would be 'balance', and
		 * 'elementaryType' would be 'address'.
		 * @param exp The expression, with any number of qualifiers.
		 * @param elementaryType The type of the field or local variable that we are currently looking in.
		 *                       Example: we are initially given the expression "a.balance". 'exp' would then be
		 * 	 *                       "balance", and the elementary type would be "address".
		 * @return The Solidity type of the expression, or void, if we came to the conclusion that the expression
		 * must be a function call.
		 */
		private String lookupTypeForDotExpressionElementaryTypeContext(String exp, String elementaryType) {
			int firstDotPos = exp.indexOf('.');
			String beforeFirstDot = firstDotPos == -1 ? exp : exp.substring(0, firstDotPos);
			String afterFirstDot = firstDotPos == -1 ? exp : exp.substring(firstDotPos + 1);
			String fieldType = null;
			if (elementaryType.equals("address")) {
				fieldType = reservedAddressFields.get(beforeFirstDot);
			} else if (typeIsArray(elementaryType)) {
				fieldType = reservedArrayFields.get(beforeFirstDot);
			}
			if (fieldType == null) {
				return "void";
			} else if (firstDotPos == -1) {
				return fieldType;
			} else {
				// The field can only be of an elementary type.
				return lookupTypeForDotExpressionElementaryTypeContext(afterFirstDot, fieldType);
			}
		}
	}

	/**
	 * This visitor is used to check whether a function/constructor/modifier body contains a return statement.
	 */
	private class SolidityCallableHasReturnStatementVisitor extends SolidityBaseVisitor<Boolean> {
		@Override public Boolean visitReturnStatement(SolidityParser.ReturnStatementContext ctx) {
			return true;
		}

		@Override public Boolean visitBlock(SolidityParser.BlockContext ctx) {
			if (ctx.statement() == null || ctx.statement().isEmpty()) {
				return false;
			}
			for (SolidityParser.StatementContext stmntCtx : ctx.statement()) {
				if (visit(stmntCtx))
					return true;
			}
			return false;
		}

		@Override public Boolean visitTerminal(TerminalNode n) { return false; }
	}
}