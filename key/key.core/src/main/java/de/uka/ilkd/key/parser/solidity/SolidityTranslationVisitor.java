package de.uka.ilkd.key.parser.solidity;

import org.antlr.v4.runtime.tree.TerminalNode;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class SolidityTranslationVisitor extends SolidityBaseVisitor<String> {
	private static final String defaultReturnVariableName = "__returnVal";

	private final StringBuilder output = new StringBuilder();
	private final VariableScopeStack varStack = new VariableScopeStack();
	private final Stack<ContractStructure> structureStack = new Stack<>();
	private Environment env = new Environment();
	private Solidity.Contract currentContract; // The contract that we are currently visiting/building
	private Solidity.Contract currentOwnerContract; // If we are visiting e.g. an inherited function, then this will be the owner
	private StringBuilder interfaceOutput = new StringBuilder();
	private String modifierUnderscoreReplacement; // What the statement '_;' is replaced with in a modifier body.
	private String modifierReturnStmntReplacement; // What "return;" is replaced with in a modifier body.

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

	/**
	 * Use this class to maintain an environment during the visiting;
	 * we have a stack of scope, where each scope has a list of variables defined in that scope.
	 * The outermost scope contains the fields of the current contract.
	 */
	public class VariableScopeStack {
		private final Deque<List<Solidity.Variable>> deque = new ArrayDeque<>();

		/**
		 * Reset the stack to only include the fields of the current owner contract (and its inherited fields).
		 */
		public void resetToContractScope() {
			clear();
			for (Solidity.Contract parent : currentOwnerContract.c3Linearization) {
				newBlock(parent.fields);
			}
		}

		public <T extends Solidity.Variable> void pushVar(T var) {
			List<Solidity.Variable> topContext = deque.peekFirst();
			if (topContext == null)
				error("Tried to declare a variable when outside of any scope.");
			topContext.add(var);

		}

		public void clear() { deque.clear(); }

		public void newBlock() { deque.addFirst(new LinkedList<>()); }

		public void newBlock(List<? extends Solidity.Variable> list) { deque.addFirst(new LinkedList<>(list)); }

		public void exitBlock() { deque.removeFirst(); }

		public Solidity.Variable getVariableFromIdentifier(String identifier) {
			for (List<Solidity.Variable> scope : deque) {
				for (Solidity.Variable var : scope) {
					if (var.name.equals(identifier) || var.getDisplayName(currentContract).equals(identifier)) {
						return var;
					}
				}
			}
			return null;
		}

		public String getTypeofIdentifier(String identifier) {
			Solidity.Variable var = getVariableFromIdentifier(identifier);
			return var == null ? null : var.typename;
		}

		public boolean hasLocalVariableWithNameOrRenamedName(String identifier) {
			for (List<Solidity.Variable> scope : deque) {
				for (Solidity.Variable var : scope) {
					if (!(var instanceof Solidity.Field) &&
							(var.name.equals(identifier) || var.renamedName.equals(identifier))) {
						return true;
					}
				}
			}
			return false;
		}

		@Override public String toString() {
			StringBuilder sb = new StringBuilder();
			for (List<Solidity.Variable> scope : deque) {
				sb.append('[');
				for (Solidity.Variable var : scope) {
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
		static Solidity.Callable mainCallable;
		static String braceFreeMainCallableBodyOutput;
		static String parentConstructorCallsOutput;
		static List<Solidity.Modifier> currentModList;
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
	private static class CallableOverloadResolutionResult {
		String displayedName;
		Solidity.Callable callable;
		Solidity.Field field; // A function call may actually be a call to a getter for a field.
		String reservedCallType; // A function call may be to a reserved function / constructor of elementary type. This is the return type.
		FunctionCallReferenceType referenceType;
		CallableOverloadResolutionResult(String displayedName, Solidity.Callable callable, Solidity.Field field,
										 String reservedCallType, FunctionCallReferenceType referenceType)
		{
			this.displayedName = displayedName; this.callable = callable;
			this.field = field; this.reservedCallType = reservedCallType; this.referenceType = referenceType;
		}
	}

	/**
	 * An instance of this class is returned after we have performed function/constructor modifier flattening.
	 * 'mainBody' contains the output for the main body of the resulting method/constructor, i.e., the one that is
	 * visible from outside the contract class, and 'externalFunction' contains the output of additional methods
	 * that were created in the process (still part of the contract output, but external to the original function).
	 */
	private static class CallableFlatteningResult {
		String mainBodyOutput;
		String externalMethodsOutput;
		CallableFlatteningResult() {}
		CallableFlatteningResult(String mainBodyOutput, String externalMethodsOutput) {
			this.mainBodyOutput = mainBodyOutput; this.externalMethodsOutput = externalMethodsOutput;
		}
	}

	private String visitCallableBody(Solidity.Callable callable) {
		String output;
		varStack.newBlock(callable.params);
		if (callable instanceof Solidity.Function) {
			structureStack.push(ContractStructure.FUNCTION_BODY);
		} else if (callable instanceof Solidity.Constructor) {
			structureStack.push(ContractStructure.CONSTRUCTOR_BODY);
		} else if (callable instanceof Solidity.Modifier) {
			structureStack.push(ContractStructure.MODIFIER_BODY);
		} else {
			error("Unknown callable type encountered.");
		}
		output = visit(callable.getBodyContext());
		structureStack.pop();
		varStack.exitBlock();
		return output;
	}

	private boolean nameIsAContract(String name) {
		return env.contracts.get(name) != null;
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
	private Optional<String> getReservedFunctionReturnTypeContractContext(String name, Solidity.Contract containingContract, boolean checkLocalVars) {
		int firstDotPos = name.indexOf(".");
		if (firstDotPos == -1) {
			String retType = Solidity.reservedFreeFunctions.get(name);
			return retType == null ? Optional.empty() : Optional.of(retType);
			/*
			if (retType != null) {
				return Optional.of(retType);
			}
			if (Solidity.typeIsElementary(name)) {
				return Optional.of(name);
			}
			return Optional.empty();

			 */
		}
		String beforeFirstDot = name.substring(0, firstDotPos);
		String afterFirstDot = name.substring(firstDotPos + 1);
		if (checkLocalVars) {
			Solidity.Variable var = varStack.getVariableFromIdentifier(beforeFirstDot);
			if (var != null) {
				if (nameIsAContract(var.typename)) {
					return getReservedFunctionReturnTypeContractContext(afterFirstDot, env.contracts.get(var.typename), false);
				}
				Solidity.Struct struct = containingContract.lookupStruct(var.typename, env);
				if (struct != null) {
					return getReservedFunctionReturnTypeStructContext(afterFirstDot, struct);
				}
				return getReservedFunctionReturnTypeElementaryTypeContext(afterFirstDot, var.typename);
			}
		}
		Solidity.Field field = containingContract.lookupField(beforeFirstDot);
		if (field != null) {
			if (nameIsAContract(field.typename)) {
				return getReservedFunctionReturnTypeContractContext(afterFirstDot, env.contracts.get(field.typename), false);
			}
			Solidity.Struct struct = containingContract.lookupStruct(field.typename, env);
			if (struct != null) {
				return getReservedFunctionReturnTypeStructContext(afterFirstDot, struct);
			}
			return getReservedFunctionReturnTypeElementaryTypeContext(afterFirstDot, field.typename);
		}
		if (nameIsAContract(beforeFirstDot))
			return getReservedFunctionReturnTypeContractContext(afterFirstDot, env.contracts.get(beforeFirstDot), false);
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
			retType = Solidity.reservedAddressFunctions.get(beforeFirstDot);
		} else if (elementaryType.equals("string")) {
			retType = Solidity.reservedStringFunctions.get(beforeFirstDot);
		} else if (elementaryType.startsWith("bytes")) {
			retType = Solidity.reservedBytesFunctions.get(beforeFirstDot);
		} else if (Solidity.typeIsArray(elementaryType)) {
			retType = Solidity.reservedArrayFunctions.get(beforeFirstDot);
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
		String msgFieldType = Solidity.reservedMsgFields.get(beforeFirstDot);
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
	private Optional<String> getReservedFunctionReturnTypeStructContext(String name, Solidity.Struct containingStruct) {
		int firstDotPos = name.indexOf(".");
		if (firstDotPos == -1) {
			// Structs do not have reserved functions.
			return Optional.empty();
		}
		String beforeFirstDot = name.substring(0, firstDotPos);
		String afterFirstDot = name.substring(firstDotPos + 1);
		for (Solidity.Variable var : containingStruct.fields) {
			if (var.name.equals(beforeFirstDot)) {
				if (nameIsAContract(var.typename))
					return getReservedFunctionReturnTypeContractContext(afterFirstDot, env.contracts.get(var.typename), false);
				Solidity.Struct struct = containingStruct.owner.lookupStruct(var.typename, env);
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

	private String removeOuterBracesFromCallableBodyOutput(String callableBodyOutput) {
		int openIndex = callableBodyOutput.indexOf('{');
		if (openIndex == -1)
			error("Supplied body does not have an opening brace.");
		int endIndex = callableBodyOutput.lastIndexOf('}');
		if (endIndex == -1)
			error("Supplied body does not have an ending brace");
		return callableBodyOutput.subSequence(openIndex + 1, endIndex).toString();
	}

	private String declareFunctionReturnVars(Solidity.Function function) {
		if (function.returnType.equals("void")) {
			return "";
		}
		else if (function.returnVars.isEmpty()) {
			return Solidity.solidityToJavaType(function.returnType, env) + " " + defaultReturnVariableName +
					" = " + defaultValueOfType(function.returnType) + ";\n";
		} else {
			StringBuilder output = new StringBuilder();
			function.returnVars.forEach(var -> output.append(
					Solidity.solidityToJavaType(var.typename, env) + " " + var.name + " = " +
							defaultValueOfType(var.typename) + ";\n"));
			return output.toString();
		}
	}

	private String makeFunctionReturnStmnt(Solidity.Function function) {
		if (function.returnType.equals("void")) {
			return "";
		} else {
			if (function.returnVars.isEmpty()) {
				return "return " + defaultReturnVariableName + ";\n";
			} else {
				// TODO: for now, we return only the first return variable. In the future, return tuples of some kind.
				Solidity.Variable firstReturnVar = function.returnVars.get(0);
				varStack.pushVar(firstReturnVar);
				return "return " + firstReturnVar.name + ";\n";
			}
		}
	}

	private String makeReturnVarAssignment(Solidity.Function function) {
		if (function.returnType.equals("void")) {
			error("Cannot assign to return variables when the function returns void.");
			return "";
		} else {
			if (function.returnVars.isEmpty()) {
				return defaultReturnVariableName + " = ";
			} else {
				// TODO: for now, we assign only to the first return variable. In the future, return tuples of some kind.
				return function.returnVars.get(0).name + " = ";
			}
		}
	}

	/**
	 * The default value of a type, as it would be in SolidiKeY, not Java. For instance, the default value of 'string'
	 * is "", not null.
	 * @param type The name of type in either Solidity or Java (it is converted to a Java type).
	 * @return The default value of the type in Solidity, as a string.
	 */
	private String defaultValueOfType(String type) {
		// TODO: for int[], the default value should be "new int[n]" (Solidity default initialization),
		//  where n is the size, but we don't know the size.
		if (nameIsAContract(type)) {
			return "new " + env.contracts.get(type).getDisplayName() + "()";
		}
		Solidity.Struct struct = currentOwnerContract.getStruct(type);
		if (struct != null) {
			return "new " + struct.getDisplayName() + "()";
		}
		return switch (Solidity.solidityToJavaType(type, env)) {
			case "int" -> "0";
			case "boolean" -> "false";
			case "String" -> "\"\"";
			case "Address" -> "(Address)(0)";
			default -> "null";
		};
	}

	/**
	 * Get a list of parent constructors that the constructor *explicitly* invokes.
	 * @return A list of parent constructors that the constructor invokes, in the invocation order.
	 */
	private List<SolidityParser.ModifierInvocationContext> getAllParentConstructorInvocations(Solidity.Constructor constructor) {
		if (constructor.isDefaultConstructor()) {
			return new LinkedList<>();
		}
		List<SolidityParser.ModifierInvocationContext> invCtxs = new LinkedList<>();
		if (constructor.ctx.modifierList() != null) {
			for (SolidityParser.ModifierInvocationContext invCtx : constructor.ctx.modifierList().modifierInvocation()) {
				String invConstrName = invCtx.identifier().getText();
				for (Solidity.Contract parent : constructor.owner.c3Linearization) {
					if (parent.name.equals(invConstrName)) {
						invCtxs.add(invCtx);
					}
				}
			}
		}
		return invCtxs;
	}

	/**
	 * Resolve a function call; given the function call expression context and the contract from which the function
	 * was called, perform overload resolution to determine which explicit function should be called.
	 * @param ctx The function call expression context.
	 * @return A tuple of 1) the name of the explicit function that is called, as it should be displayed in
	 *                       the current contract, and
	 *                    2) the function itself as a 'Solidity.Function', containing e.g. the context and signature.
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
			cast					type()
			 */
		// TODO: we may not call an external function unless 'this' is used. Currently, this is not checked,
		//  and could lead to function overload resolution being wrong in very specific situations (?)

		// Check if we have a type cast
		String fctName = ctx.expression().getText();
		if (Solidity.typeIsElementary(fctName)) {
			// type(...) => (type)(...)
			String displayedName = "(" + Solidity.solidityToJavaType(fctName, env) + ")";
			return new CallableOverloadResolutionResult(displayedName, null, null, fctName, FunctionCallReferenceType.INTERNAL);
		}

		// If the function name is reserved, we output it as in (no renaming).
		Optional<String> reservedFunctionType = getReservedFunctionReturnTypeContractContext(fctName, currentOwnerContract, true);
		if (reservedFunctionType.isPresent()) {
			return new CallableOverloadResolutionResult(fctName, null, null, reservedFunctionType.get(), FunctionCallReferenceType.INTERNAL);
		}

		String objectName = fctName;
		String comparableName = fctName;
		// Find the type of function call (above table)
		FunctionCallReferenceType referenceType;
		boolean isConstructorCall = false;
		int firstDotPos = fctName.indexOf('.');
		if (firstDotPos == -1) {
			referenceType = FunctionCallReferenceType.INTERNAL;
			// TODO: Currently, calls such as "new A()" gets turned into a function call to "newA" (ctx.expression). Fix?
			// Currently, Solidity allows one to use "new" only on contract types and arrays.
			isConstructorCall = fctName.startsWith("new") &&
					(nameIsAContract(fctName.substring("new".length())) || Solidity.typeIsArray(fctName.substring("new".length())));
		} else {
			objectName = fctName.substring(0, firstDotPos);
			comparableName = fctName.substring(firstDotPos + 1);
			if (objectName.equals("this")) {
				referenceType = FunctionCallReferenceType.THIS;
			} else if (objectName.equals("super")) {
				referenceType = FunctionCallReferenceType.SUPER;
			} else if (nameIsAContract(objectName)) {
				if (env.contracts.get(objectName).type == Solidity.ContractType.LIBRARY)
					referenceType = FunctionCallReferenceType.LIBRARY;
				else
					referenceType = FunctionCallReferenceType.CONTRACT;
			} else if (varStack.getVariableFromIdentifier(objectName) != null) {
				referenceType = FunctionCallReferenceType.OBJECT;
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
				Solidity.Contract ownerContract = env.contracts.get(ownerContractName);
				if (ownerContract == null)
					error("Could not locate contract " + ownerContractName);
				String displayName = "new " + ownerContract.getDisplayName();
				return new CallableOverloadResolutionResult(displayName, ownerContract.constructor, null,null, referenceType);
			} else if (Solidity.typeIsElementary(type) || Solidity.typeIsArray(type)) {
				String displayName = "new " + Solidity.solidityToJavaType(type, env);
				return new CallableOverloadResolutionResult(displayName, null, null, type, referenceType);
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
			Solidity.Contract library = env.contracts.get(objectName);
			Solidity.Function libFun = library.getFunction(comparableName, resolvedArgs, currentOwnerContract, env, true);
			if (libFun == null) {
				error("Could not find function " + comparableName + " in library " + library.name);
			} else {
				String displayedName = library.name + "." + libFun.name;
				return new CallableOverloadResolutionResult(displayedName, libFun, null, null, referenceType);
			}
		}

		// Look for calls to attached library functions (these come from "Using For" declarations).
		//  Here, the first parameter of the original library function should be missing in the argument list,
		//  if that parameter's type was the same as the type of the object the function was called on.
		//  This is so that the function can be called as a member function, and the first parameter is implicit.
		String typeOfThis = switch (referenceType) {
			case INTERNAL, THIS -> currentOwnerContract.name;
			case CONTRACT -> objectName;
			case SUPER -> currentContract.getContractBefore(currentOwnerContract.name).name;
			case OBJECT -> varStack.getTypeofIdentifier(objectName);
			default -> error("Unrecognizable function call reference type.");
		};
		List<String> resolvedArgsPrependedWithThis = new LinkedList<>(resolvedArgs);
		resolvedArgsPrependedWithThis.add(0, typeOfThis);

		for (Solidity.Function libFun : currentOwnerContract.getAttachedLibraryFunctionsForType(typeOfThis)) {
			if (libFun.name.equals(comparableName) &&
					Solidity.argTypesMatchesFunctionParams(resolvedArgsPrependedWithThis, libFun.getParamTypeNames(),
							libFun, currentOwnerContract, env, true)) {
				String displayedName = libFun.owner.name + "." + libFun.name;
				return new CallableOverloadResolutionResult(displayedName, libFun, null, null, referenceType);
			}
		}

		// No library functions were found. If the object type is not a contract type, at this point, no more functions remain
		if (referenceType == FunctionCallReferenceType.OBJECT && !nameIsAContract(typeOfThis)) {
			error("Could not resolve function call " + fctName +  " in contract " + currentOwnerContract.name);
		}

		// Perform the linearization walk to look for self-defined or inherited functions.
		Solidity.Contract caller; // Whose linearization to use.
		String startContractName; // The walking of the linearization list should start from this contract.
		if (referenceType == FunctionCallReferenceType.OBJECT) {
			String typeName = varStack.getTypeofIdentifier(objectName);
			if (nameIsAContract(typeName)) {
				caller = env.contracts.get(typeName);
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
		Solidity.Function resolvedFun = null;
		Solidity.Field resolvedField = null;
		String displayName = null;
		Iterator<Solidity.Contract> reverseIt = caller.c3Linearization.descendingIterator();
		while (reverseIt.hasNext()) {
			Solidity.Contract parent = reverseIt.next();
			if (!startContractFound) {
				if (parent.name.equals(startContractName)) {
					startContractFound = true;
					if (skipSearchInStartContract) {
						continue;
					}
				} else {
					continue;
				}
			}
			// Check if the parent has the function
			Solidity.Function fun = parent.getFunction(comparableName, resolvedArgs, currentOwnerContract, env, true);
			if (fun != null) {
				boolean funIsVisible = fun.visibility != Solidity.FunctionVisibility.PRIVATE ||
						(referenceType == FunctionCallReferenceType.OBJECT && caller.name.equals(currentOwnerContract.name)) ||
						(referenceType != FunctionCallReferenceType.OBJECT && parent.name.equals(caller.name));
				if (!funIsVisible)
					continue;
				resolvedFun = fun;
				String funPrefix;
				if (referenceType == FunctionCallReferenceType.THIS) {
					funPrefix = "this.";
				} else if (referenceType == FunctionCallReferenceType.OBJECT) {
					Solidity.Variable var = varStack.getVariableFromIdentifier(objectName);
					funPrefix = var.getDisplayName(currentContract) + ".";
				} else {
					funPrefix = "";
				}
				displayName = funPrefix + resolvedFun.getDisplayName(caller);
				break;
			}
			// Check if the parent has the field (getter)
			if (resolvedArgs.isEmpty()) {
				Solidity.Field field = parent.getField(comparableName);
				if (field != null) {
					boolean fieldIsVisible = field.visibility != Solidity.FieldVisibility.PRIVATE ||
							(referenceType == FunctionCallReferenceType.OBJECT && caller.name.equals(currentOwnerContract.name)) ||
							(referenceType != FunctionCallReferenceType.OBJECT && parent.name.equals(caller.name));
					if (!fieldIsVisible)
						continue;
					resolvedField = field;
					displayName = resolvedField.getDisplayName(caller);
					if (referenceType == FunctionCallReferenceType.OBJECT) {
						Solidity.Variable var = varStack.getVariableFromIdentifier(objectName);
						displayName = var.getDisplayName(currentContract) + "." + displayName;
					}
				}
			}
		}
		if (resolvedFun == null && resolvedField == null) {
			error("Could not resolve function call for function " + comparableName +
					" from contract " + caller.name);
		}
		return new CallableOverloadResolutionResult(displayName, resolvedFun, resolvedField, null, referenceType);
	}

	/**
	 * Resolve a modifier call; given the modifier invocation context and the contract from which the modifier was called,
	 * perform overload (technically override; modifiers cannot be overloaded) resolution to determine which explicit
	 * modifier should be called.
	 * @param ctx The modifier invocation context.
	 * @return A tuple of 1) the name of the explicit modifier that is called, as it should be displayed in
	 *                       the current contract, and
	 *                    2) the modifier itself as a 'Solidity.Modifier', containing e.g. the context and signature.
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

		Solidity.Modifier mod;
		if (isDirectCall) {
			Solidity.Contract parent = env.contracts.get(contractName);
			if (parent == null) {
				error("Contract " + currentOwnerContract.name + " calls modifier " + modName +
						", but contract " + contractName + " does not exist.");
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
			return new CallableOverloadResolutionResult(displayName, mod, null, null, referenceType);
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
	private CallableFlatteningResult createFlattenedCallable(Solidity.Callable callable,
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

		List<Solidity.Modifier> mods = new LinkedList<>();
		modCtxs.forEach(modCtx -> {
			CallableOverloadResolutionResult overloadResult = resolveModifierCall(modCtx);
			if (overloadResult.callable == null) {
				error("Could not resolve modifier call to " + modCtx.identifier());
			}
			Solidity.Modifier mod = (Solidity.Modifier)(overloadResult.callable);
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
		for (Solidity.Modifier mod : mods) {
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
		mainBodyOutput.append(result.mainBodyOutput);
		mainBodyOutput.append("\n}\n");
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
	private CallableFlatteningResult flattenCallableWithModInlining(Solidity.Callable callable,
																	String braceFreeCallableBodyOutput,
																	String parentConstructorCallsOutput,
																	List<Solidity.Modifier> mods,
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
			externalOutput.append(callable instanceof Solidity.Function ? Solidity.solidityToJavaType(callable.returnType, env) : "void");
			externalOutput.append(" ");
			externalOutput.append(ModifierFlattening.mainCallable.getModFreeDisplayName(currentContract));
			externalOutput.append(callable.buildParamListWithParen(env));
			externalOutput.append("{\n");
			// Declare return variables at the top of the function body, and return at the end.
			// This may produce a Java program that does not compile (unreachable code), but we don't care.
			boolean declareReturnVars = ModifierFlattening.mainCallable instanceof Solidity.Function;
			if (declareReturnVars) {
				externalOutput.append(declareFunctionReturnVars((Solidity.Function)(ModifierFlattening.mainCallable)));
			}
			externalOutput.append(ModifierFlattening.braceFreeMainCallableBodyOutput);
			if (declareReturnVars) {
				externalOutput.append(makeFunctionReturnStmnt((Solidity.Function)(ModifierFlattening.mainCallable)));
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
					if (ModifierFlattening.mainCallable instanceof Solidity.Function &&
							!ModifierFlattening.mainCallable.returnType.equals("void"))
					{
						output.append(makeReturnVarAssignment((Solidity.Function)ModifierFlattening.mainCallable));
					}
					output.append(ModifierFlattening.mainCallable.getModFreeDisplayName(currentContract));
					output.append(ModifierFlattening.mainCallable.buildArgListWithParen());
					output.append(";");
				}
				default -> error("Unrecognized modifier flattening mode encountered.");
			}

		} else {
			Solidity.Modifier currentMod = ModifierFlattening.currentModList.get(ModifierFlattening.currentModPos);

			// At the start of the flattened body, declare function return variables, if any.
			boolean declareReturnVarsAndReturnStmnt = ModifierFlattening.currentModPos == 0 &&
					ModifierFlattening.mainCallable instanceof Solidity.Function;
			if (declareReturnVarsAndReturnStmnt) {
				output.append(declareFunctionReturnVars((Solidity.Function)ModifierFlattening.mainCallable));
			}
			// Visit the body
			output.append(removeOuterBracesFromCallableBodyOutput(visitCallableBody(currentMod)));
			// At the end, return, unless return type is void.
			if (declareReturnVarsAndReturnStmnt) {
				output.append(makeFunctionReturnStmnt((Solidity.Function)ModifierFlattening.mainCallable));
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
	private CallableFlatteningResult flattenCallableWithModCalling(Solidity.Callable callable,
																   String braceFreeCallableBodyOutput,
																   String parentConstructorCallsOutput,
																   List<Solidity.Modifier> mods,
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

		HashMap<Solidity.Modifier, Integer> numberOfOccurrences = new HashMap<>();
		HashMap<Solidity.Modifier, Integer> numberOfTimesVisited = new HashMap<>();
		mods.forEach(mod -> {
			numberOfOccurrences.merge(mod, 1, Integer::sum); // Add 1 to the count, or if null, make it 1.
			numberOfTimesVisited.putIfAbsent(mod, 0); // Start with 0 initially; below, we do the actual "visiting".
		});

		// output in the form of functions created in addition to the "original"/base function, i.e.,
		// the one that is actually called from outside the contract.
		StringBuilder externalOutput = new StringBuilder();

		// Create the function for the original function/constructor without any mods.
		String returnType = null;
		if (callable instanceof Solidity.Constructor) {
			returnType = "void";
		} else if (callable instanceof Solidity.Function) {
			returnType = Solidity.solidityToJavaType(callable.returnType, env);
		} else {
			error("Illegitimate Solidity.Callable type given to flattenCallableWithModCalling().");
		}
		externalOutput.append("private " + returnType + " " + callable.getModFreeDisplayName(currentContract));
		externalOutput.append(callable.buildParamListWithParen(env));
		externalOutput.append("{\n");
		// Declare return variables at the top of the function body, and return at the end.
		// This may produce a Java program that does not compile (unreachable code), but we don't care.
		boolean declareReturnVars = ModifierFlattening.mainCallable instanceof Solidity.Function;
		if (declareReturnVars) {
			externalOutput.append(declareFunctionReturnVars((Solidity.Function)(ModifierFlattening.mainCallable)));
		}
		externalOutput.append(braceFreeCallableBodyOutput);
		if (declareReturnVars) {
			externalOutput.append(makeFunctionReturnStmnt((Solidity.Function)(ModifierFlattening.mainCallable)));
		}
		externalOutput.append("\n}\n\n");

		// For each modifier in the list, create a new Java method with the same name, but prefixed with the
		// callable name. If a modifier occurs multiple times, we create one function per modifier occurrence, since
		// whatever '_;' will be replaced with depends on where in the modifier list the modifier is called.
		// First, find what '_;' should actually be replaced with, as well as return statements.
		if (callable instanceof Solidity.Function && !callable.returnType.equals("void")) {
			modifierReturnStmntReplacement = "return " + defaultReturnVariableName + ";";
		} else {
			modifierReturnStmntReplacement = "return;";
		}

		// Save the previous owner and then restore it after all modifiers have been visited.
		// This is because we need to set the owner contract equal to the owner of the modifier when we visit it.
		Solidity.Contract prevOwnerContract = currentOwnerContract;

		int modIndex = -1;
		for (Solidity.Modifier mod : mods) {
			modIndex++;
			boolean isTheLastModifier = modIndex == mods.size() - 1;

			currentOwnerContract = mod.owner;
			varStack.resetToContractScope();

			structureStack.push(ContractStructure.CALLABLE_HEADER);

			// Find what the underscore replacement should be. When the modifier block is visited and
			// an '_;' is encountered (see visitTerminal()), the replacement takes place.
			StringBuilder underscoreReplacement = new StringBuilder();
			if (callable instanceof Solidity.Function && !returnType.equals("void")) {
				underscoreReplacement.append(defaultReturnVariableName + " = ");
			}
			if (isTheLastModifier) {
				underscoreReplacement.append(callable.getModFreeDisplayName(currentContract) + "(msg,");
				callable.params.forEach(param -> underscoreReplacement.append(
						ModifierFlattening.getDisplayNameOfCallableParamInModifier(param.name) + ","));
				underscoreReplacement.deleteCharAt(underscoreReplacement.length() - 1);
			} else {
				Solidity.Modifier nextMod = mods.get(modIndex + 1);
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
			if (callable instanceof Solidity.Function) {
				externalOutput.append(Solidity.solidityToJavaType(callable.returnType, env) + " ");
			} else {
				externalOutput.append("void ");
			}
			String shownModifierName = mod.getDisplayName(currentContract, callable,
					numberOfTimesVisited.get(mod), numberOfOccurrences.get(mod));
			externalOutput.append(shownModifierName);
			externalOutput.append('(');
			externalOutput.append(mod.buildParamList(env));
			externalOutput.append(',');
			callable.params.forEach(param ->
					externalOutput.append(Solidity.solidityToJavaType(param.typename, env) + " " +
							ModifierFlattening.getDisplayNameOfCallableParamInModifier(param.name) + ","));
			externalOutput.deleteCharAt(externalOutput.length() - 1);
			externalOutput.append("){\n");

			structureStack.pop();

			boolean declareModReturnVar = callable instanceof Solidity.Function && !callable.returnType.equals("void");

			if (declareModReturnVar) {
				externalOutput.append(Solidity.solidityToJavaType(callable.returnType, env) + " " +
						defaultReturnVariableName + " = " + defaultValueOfType(callable.returnType) + ";");
			}

			externalOutput.append(removeOuterBracesFromCallableBodyOutput(visitCallableBody(mod)));
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
		if (callable instanceof Solidity.Function && !callable.returnType.equals("void")) {
			bodyOutput.append("return ");
		}
		Solidity.Modifier firstMod = mods.get(0);
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
		SolidityPreVisitor preVisitor = new SolidityPreVisitor();
		env = preVisitor.visit(ctx);
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
		Solidity.Contract contract = env.contracts.get(contractName);
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
			contract.inheritanceList.forEach(c -> interfaceOutput.append(" " + c.name + ","));
			interfaceOutput.deleteCharAt(interfaceOutput.length()-1);
		}
		interfaceOutput.append(" {\n");

		if (contract.type == Solidity.ContractType.CONTRACT) {
			if (contract.isAbstract) {
				classOutput.append("abstract ");
			}
			classOutput.append("class " + contract.getDisplayName() +
					" extends Address implements " + contractName + " {\n");
			ctx.contractPart().stream().forEach(part -> classOutput.append(visit(part) + '\n'));
		} else if (contract.type == Solidity.ContractType.INTERFACE) {
			// interfaceOutput is appended to manually when we see a func decl, struct def, etc.
			ctx.contractPart().stream().forEach(part -> visit(part));
		} else if (contract.type == Solidity.ContractType.LIBRARY) {
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
		if (contract.type == Solidity.ContractType.CONTRACT) {
			for (Solidity.Contract parent : contract.c3Linearization) {
				if (parent.equals(currentContract))
					continue;
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
		if (contract.type != Solidity.ContractType.LIBRARY) {
			output.append(interfaceOutput);
		}
		if (contract.type != Solidity.ContractType.INTERFACE) {
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

		Solidity.Field field = currentOwnerContract.getField(ctx.identifier().getText());

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
		String shownTypename = Solidity.solidityToJavaType(field.typename, env);
		Solidity.DataLocation dataLocation = Solidity.DataLocation.STORAGE;
		String dataLocationAnnotation = Solidity.getDataLocationAnnotation(dataLocation);

		output.append(" " + shownTypename + " " + dataLocationAnnotation + " " + displayName);

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
		Solidity.Struct struct = currentOwnerContract.lookupStruct(ctx.identifier().getText(), env);
		if (struct == null) {
			error("Could not locate struct " + ctx.identifier().getText() + " in contract " + currentOwnerContract.name);
		}
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

		Solidity.Constructor constructor = currentOwnerContract.constructor;

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

		String parameters = constructor.buildParamListWithParen(env);
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

		StringBuilder braceFreeBodyOutput = new StringBuilder(removeOuterBracesFromCallableBodyOutput(visitCallableBody(constructor)));

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
					int linearizationPos = 0;
					for (Solidity.Contract parent : currentOwnerContract.c3Linearization) {
						if (parent.name.equals(identifier)) {
							break;
						}
						++linearizationPos;
					}
					boolean isConstructorInvocation = linearizationPos != currentOwnerContract.c3Linearization.size();
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
				for (Solidity.Contract parent : currentContract.c3Linearization) {
					Solidity.Constructor parentConstructor = parent.constructor;
					List<SolidityParser.ModifierInvocationContext> parentConstructorInvocations =
							getAllParentConstructorInvocations(parentConstructor);
					// Merge the two lists
					constructorCalls = Stream.of(constructorCalls, parentConstructorInvocations)
							.flatMap(Collection::stream)
							.collect(Collectors.toList());
				}

				// Go through all the parents of the current contract and locate the corresponding constructor invocations.
				// Add to the constructor body output an invocation of the constructors with the found arguments.
				// If an invocation can not be found, simply add "CImpl(msg);", where C is the name of the parent, to the output,
				// if the constructor of C is parameter-free. Otherwise, throw an error.
				for (Solidity.Contract parent : currentContract.c3Linearization) {
					if (parent.equals(currentContract))
						continue;
					// Locate the invocation of the parent constructor.
					// If there are two invocations, this is undefined behaviour (Solidity program would not compile)
					boolean invFound = false;
					for (SolidityParser.ModifierInvocationContext invCtx : constructorCalls) {
						if (invCtx.identifier().getText().equals(parent.name)) {
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
						if (parent.constructor.params.isEmpty()) {
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
		Solidity.Function function = currentOwnerContract.getFunction(funName, argTypes, currentOwnerContract, env, false);
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
		String parameters = function.buildParamListWithParen(env);
		String returnType = Solidity.solidityToJavaType(function.returnType, env);
		String fctHeader = visibility + (currentContract.type == Solidity.ContractType.LIBRARY ? " static " : " ") +
				(function.isAbstract ? "abstract " : "") +
				Solidity.getDataLocationAnnotation(function.returnVarDataLocation) + " " +
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
		if (function.isAbstract || currentContract.type == Solidity.ContractType.INTERFACE) {
			return "";
		} else {
			StringBuilder braceFreeBodyOutput = new StringBuilder(removeOuterBracesFromCallableBodyOutput(visitCallableBody(function)));
			if (ctx.modifierList().modifierInvocation().isEmpty()) {
				// Declare return variables at the top of the function body, and return at the end.
				// This may produce a Java program that does not compile (unreachable code), but we don't care.
				braceFreeBodyOutput.insert(0, "{\n" + declareFunctionReturnVars(function));
				braceFreeBodyOutput.append(makeFunctionReturnStmnt(function) + "\n}");
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
		String shownTypename = Solidity.solidityToJavaType(typename, env);

		Solidity.Variable var = new Solidity.Variable(identifier, typename);

		// If the variable is shadowing a local variable (or function parameter), rename it
		boolean localVarExists = varStack.hasLocalVariableWithNameOrRenamedName(identifier);
		if (localVarExists) {
			int counter = 0;
			String suggestedName;
			do {
				suggestedName = identifier + "_" + counter++;
			} while (varStack.hasLocalVariableWithNameOrRenamedName(suggestedName));
			var.renamedName = suggestedName;
		}

		varStack.pushVar(var);

		if (ctx.storageLocation() == null) {
			if (structureStack.peek() == ContractStructure.STRUCT) {
				var.dataLocation = Solidity.DataLocation.STORAGE;
			} else { // Local variable
				// The data location must be specified for reference types. For value types, it is irrelevant, and can be omitted.
				var.dataLocation = Solidity.DataLocation.UNSPECIFIED;
			}
		} else {
			var.dataLocation = Solidity.DataLocation.stringToLocation(visit(ctx.storageLocation()));
		}
		String dataLocationAnnotation = Solidity.getDataLocationAnnotation(var.dataLocation);

		return shownTypename + (dataLocationAnnotation.equals("") ? " " : " " + dataLocationAnnotation + " ") +
				(localVarExists ? var.renamedName : identifier);
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
	@Override public String visitStorageLocation(SolidityParser.StorageLocationContext ctx) {
		return ctx.getText();
	}

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
			output += " else " + _else;
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
		String fctName = ctx.expression().getText();

		CallableOverloadResolutionResult overload = resolveFunctionCall(ctx);
		Solidity.Callable resolvedCallable = overload.callable;
		boolean functionIsAGetter = overload.field != null; // a function call can "disguise" itself as a call to a getter for a field
		String displayedName = overload.displayedName;
		FunctionCallReferenceType resolvedReferenceType = overload.referenceType;
		String reservedFunctionType = overload.reservedCallType;

		if (functionIsAGetter) {
			return displayedName;
		}

		StringBuffer arguments;
		// Do not append the "msg" argument if the call is made to a built-in Solidity function (or cast).
		boolean skipMsgArg = reservedFunctionType != null;

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
		boolean addThisArg = resolvedCallable instanceof Solidity.Function &&
				((Solidity.Function)resolvedCallable).isLibraryFunction &&
				resolvedReferenceType != FunctionCallReferenceType.LIBRARY &&
				currentContract.type != Solidity.ContractType.LIBRARY;
		if (addThisArg) {
			String thisArg;
			if (resolvedReferenceType == FunctionCallReferenceType.OBJECT) {
				String obj = fctName.substring(0, fctName.indexOf("."));
				Solidity.Variable var = varStack.getVariableFromIdentifier(obj);
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

		Solidity.Variable var = varStack.getVariableFromIdentifier(identifier);
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
		if (var instanceof Solidity.Field) {
			return switch (structureStack.peek()) {
				case CALLABLE_INVOCATION, CONSTRUCTOR_BODY, FUNCTION_BODY, MODIFIER_BODY, FIELD_DECL_RIGHT ->
						var.getDisplayName(currentContract);
				default -> identifier;
			};
		} else if (var instanceof Solidity.Variable) { // local variable or parameter
			// The variable may be renamed (from shadowing). If not, we have var.renamedName.equals(var.name)
			identifier = var.renamedName;
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

	/**
	 * This visitor is used to get the (Solidity) type of a Solidity expression.
	 * This is used so that proper function overloading can occur when we encounter a function call,
	 * by examining the types of the arguments given.
	 */
	private class SolidityExpressionTypeVisitor extends SolidityBaseVisitor<String> {
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
			SolidityTranslationVisitor.CallableOverloadResolutionResult result = resolveFunctionCall(ctx);
			if (result.callable != null) {
				return result.callable.returnType;
			} else if (result.field != null) {
				return result.field.typename;
			} else if (result.reservedCallType != null) {
				return result.reservedCallType;
			} else {
				error("Unsuccessful function overload resolution when visiting a function call expression for " +
						fctName + " in contract " + currentContract.name);
				return "void";
			}
		}

		@Override public String visitNotExpression(SolidityParser.NotExpressionContext ctx) {
			return "bool";
		}

		@Override public String visitUnaryAdditiveExpression(SolidityParser.UnaryAdditiveExpressionContext ctx) {
			return visitChildren(ctx);
		}

		@Override public String visitPrimaryExpression(SolidityParser.PrimaryExpressionContext ctx) {
			if (ctx.BooleanLiteral() != null) {
				return "bool";
			} else if (ctx.numberLiteral() != null) {
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
		private String lookupTypeForDotExpressionContractContext(String exp, Solidity.Contract containingContract, boolean checkLocalVars) {
			Solidity.Enum enum_ = containingContract.lookupEnum(exp, env);
			if (enum_ != null)
				return enum_.getDisplayName();
			Solidity.Struct struct = containingContract.lookupStruct(exp, env);
			if (struct != null)
				return struct.getDisplayName();
			int firstDotPos = exp.indexOf(".");
			if (firstDotPos == -1) {
				if (checkLocalVars) {
					Solidity.Variable var = varStack.getVariableFromIdentifier(exp);
					if (var != null)
						return var.typename;
				}
				Solidity.Field field = containingContract.lookupField(exp);
				if (field != null)
					return field.typename;
				Solidity.Contract contract = env.contracts.get(exp);
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
					return lookupTypeForDotExpressionContractContext(afterFirstDot, env.contracts.get(beforeFirstDot), false);
				} else {
					if (checkLocalVars) {
						Solidity.Variable var = varStack.getVariableFromIdentifier(beforeFirstDot);
						if (var != null) {
							if (nameIsAContract(var.typename)) {
								return lookupTypeForDotExpressionContractContext(afterFirstDot, env.contracts.get(var.typename), false);
							}
							Solidity.Struct struct_ = containingContract.lookupStruct(var.typename, env);
							if (struct_ != null) {
								return lookupTypeForDotExpressionStructContext(afterFirstDot, struct_);
							}
							return lookupTypeForDotExpressionElementaryTypeContext(afterFirstDot, var.typename);
						}
					}
					Solidity.Field field = containingContract.lookupField(beforeFirstDot);
					if (field != null) {
						if (nameIsAContract(field.typename)) {
							return lookupTypeForDotExpressionContractContext(afterFirstDot, env.contracts.get(field.typename), false);
						}
						Solidity.Struct struct_ = containingContract.lookupStruct(field.typename, env);
						if (struct_ != null) {
							return lookupTypeForDotExpressionStructContext(afterFirstDot, struct_);
						}
						return lookupTypeForDotExpressionElementaryTypeContext(afterFirstDot, field.typename);
					}
					if (nameIsAContract(beforeFirstDot))
						return lookupTypeForDotExpressionContractContext(afterFirstDot, env.contracts.get(beforeFirstDot), false);
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
		private String lookupTypeForDotExpressionStructContext(String exp, Solidity.Struct containingStruct) {
			int firstDotPos = exp.indexOf(".");
			String beforeFirstDot = firstDotPos == -1 ? exp : exp.substring(0, firstDotPos);
			String afterFirstDot = firstDotPos == -1 ? exp : exp.substring(firstDotPos + 1);
			String type = null;
			for (Solidity.Variable var : containingStruct.fields) {
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
				return lookupTypeForDotExpressionContractContext(afterFirstDot, env.contracts.get(type), false);
			Solidity.Struct struct = containingStruct.owner.lookupStruct(type, env);
			if (struct != null)
				return lookupTypeForDotExpressionStructContext(afterFirstDot, struct);
			Solidity.Enum enum_ = containingStruct.owner.lookupEnum(type, env);
			if (enum_ != null)
				return enum_.getDisplayName();
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
			String msgFieldType = Solidity.reservedMsgFields.get(beforeFirstDot);
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
				fieldType = Solidity.reservedAddressFields.get(beforeFirstDot);
			} else if (Solidity.typeIsArray(elementaryType)) {
				fieldType = Solidity.reservedArrayFields.get(beforeFirstDot);
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
}