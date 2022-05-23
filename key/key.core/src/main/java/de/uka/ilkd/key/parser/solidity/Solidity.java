package de.uka.ilkd.key.parser.solidity;

import java.util.*;

public class Solidity {
    public enum ContractType {
        CONTRACT, INTERFACE, LIBRARY
    }

    public enum FieldVisibility {
        PUBLIC, INTERNAL, PRIVATE
    }

    public enum FunctionVisibility {
        EXTERNAL, PUBLIC, INTERNAL, PRIVATE
    }

    public enum DataLocation {
        CALLDATA, MEMORY, STORAGE, UNSPECIFIED;

        public static DataLocation stringToLocation(String loc) {
            return switch (loc) {
                case "calldata" -> DataLocation.CALLDATA;
                case "memory" -> DataLocation.MEMORY;
                case "storage" -> DataLocation.STORAGE;
                default -> DataLocation.UNSPECIFIED;
            };
        }
    }

    // TODO: model abi, global vars 'block' and 'tx'.

    public static final List<String> elementarySolidityTypes = Arrays.asList(
            "void", "bool", "uint", "uint8", "uint16", "uint24", "uint32", "uint40", "uint48", "uint56", "uint64",
            "uint72", "uint80", "uint88", "uint96", "uint104", "uint112", "uint120", "uint128", "uint136", "uint144",
            "uint152", "uint160", "uint168", "uint176", "uint184", "uint192", "uint200", "uint208", "uint216",
            "uint224", "uint232", "uint240", "uint248", "uint256", "int", "int8", "int16", "int24", "int32", "int40",
            "int48", "int56", "int64", "int72", "int80", "int88", "int96", "int104", "int112", "int120", "int128",
            "int136", "int144", "int152", "int160", "int168", "int176", "int184", "int192", "int200", "int208",
            "int216", "int224", "int232", "int240", "int248", "int256", "address", "address payable", "bytes", "bytes1",
            "bytes2", "bytes3", "bytes4", "bytes5", "bytes6", "bytes7", "bytes8", "bytes9", "bytes10", "bytes11",
            "bytes12", "bytes13", "bytes14", "bytes15", "bytes16", "bytes17", "bytes18", "bytes19", "bytes20",
            "bytes21", "bytes22", "bytes23", "bytes24", "bytes25", "bytes26", "bytes27", "bytes28", "bytes29",
            "bytes30", "bytes31", "bytes32", "string"
    );

    // https://docs.soliditylang.org/en/v0.8.12/units-and-global-variables.html
    public static final Map<String, String> reservedFreeFunctions = new HashMap<>() {
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

    public static final Map<String, String> reservedAddressFunctions = new HashMap<>() {
        {
            put("call", "(bool, bytes)");
            put("delegatecall", "(bool, bytes)");
            put("send", "bool");
            put("staticcall", "(bool, bytes)");
            put("transfer", "void");
        }
    };

    public static final Map<String, String> reservedAddressFields = new HashMap<>() {
        {
            put("balance", "uint256");
            put("code", "bytes");
            put("codehash", "bytes32");
        }
    };

    public static final Map<String, String> reservedMsgFields = new HashMap<>() {
        {
            put("data", "bytes");
            put("sender", "address");
            put("sig", "bytes4");
            put("value", "uint");
        }
    };

    public static final Map<String, String> reservedBytesFunctions = new HashMap<>() {
        {
            put("concat", "bytes");
        }
    };

    public static final Map<String, String> reservedStringFunctions = new HashMap<>() {
        {
            put("concat", "string");
        }
    };

    public static final Map<String, String> reservedArrayFields = new HashMap<>() {
        {
            put("length", "uint");
        }
    };

    public static final Map<String, String> reservedArrayFunctions = new HashMap<>() {
        {
            put("pop", "void");
            put("push", "void");
        }
    };

    public static final String logicalVarType = "logical";

    public static abstract class Callable {
        public String name;
        public Contract owner;
        public String returnType; // Solidity type
        public DataLocation returnVarDataLocation = DataLocation.UNSPECIFIED;
        public boolean isPayable;
        public LinkedList<Variable> params = new LinkedList<>();
        public int inputFileStartLine;

        public Callable(String name, Contract owner) {
            this.name = name;
            this.owner = owner;
        }

        public LinkedList<String> getParamTypeNames() {
            LinkedList<String> typeNames = new LinkedList<>();
            params.forEach(param -> typeNames.add(param.typename));
            return typeNames;
        }

        public String buildParamList(Environment env) {
            StringBuilder output = new StringBuilder("Message msg,");
            params.forEach(param -> output.append(param.getJavaDeclaration(env) + ','));
            output.deleteCharAt(output.length() - 1);
            return output.toString();
        }

        public String buildParamListWithParen(Environment env) {
            return "(" + buildParamList(env) + ")";
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

        public boolean hasReturnStatement() {
            SolidityCallableHasReturnStatementVisitor visitor = new SolidityCallableHasReturnStatementVisitor();
            return visitor.visitBlock(getBodyContext());
        }

        /**
         * Get the name of the callable as it would be displayed from the POV of 'callingContract'
         * (either as a definition or call). I.e., if the callable has been imported from another contract,
         * the display name may contain as a prefix the name of the contract that originally implemented the callable.
         * @param callingContract The contract in which the callable should 'displayed' (called or defined).
         * @return The display name.
         */
        public abstract String getDisplayName(Contract callingContract);

        /**
         * Get the name of the callable as it would be displayed from the POV of 'callingContract', if the callable
         * has undergone modifier flattening, and this is the version of the callable free of modifiers.
         * @param callingContract The contract in which the callable should 'displayed' (called or defined).
         * @return The modifier-free display name.
         */
        public abstract String getModFreeDisplayName(Contract callingContract);

        /**
         * Checks if there exists an override of this callable anywhere in the inheritance tree of 'callingContract'.
         * @param callingContract The contract whose C3 linearization will be checked for overrides.
         * @return True if there exists an override, otherwise false.
         */
        public abstract boolean hasOverride(Contract callingContract);

        public abstract SolidityParser.BlockContext getBodyContext();
    }

    public static class Function extends Callable {
        public SolidityParser.FunctionDefinitionContext ctx;
        public FunctionVisibility visibility;
        public boolean isVirtual;
        public boolean overrides;
        public boolean isAbstract;
        public boolean isPure;
        public boolean isView;
        public boolean isLibraryFunction;
        public List<Variable> returnVars = new LinkedList<>();

        public Function(String name, Contract owner) { super(name, owner); }

        @Override
        public String getDisplayName(Contract callingContract) {
            if (!this.owner.equals(callingContract) && this.hasOverride(callingContract)) {
                return "__" + owner.name + "__" + name;
            } else {
                return name;
            }
        }

        @Override
        public String getModFreeDisplayName(Contract callingContract) {
            String normalDisplayName = getDisplayName(callingContract);
            if (normalDisplayName.startsWith("__")) {
                return "__unmod" + normalDisplayName;
            } else {
                return "__unmod__" + normalDisplayName;
            }
        }

        @Override
        public SolidityParser.BlockContext getBodyContext() { return ctx.block(); }

        @Override
        public boolean hasOverride(Contract callingContract) {
            boolean functionFound = false;
            for (Contract parent : callingContract.c3Linearization) {
                for (Function parentFunction : parent.functions) {
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
    }

    public static class Constructor extends Callable {
        public SolidityParser.ConstructorDefinitionContext ctx;

        public Constructor(Contract owner) {
            super(owner.name, owner);
            returnType = owner.name;
        }

        @Override public String getDisplayName(Contract callingContract) { return getContractDisplayName(owner.name); }

        @Override public String getModFreeDisplayName(Contract callingContract) {
            return "__unmod__" + getDisplayName(callingContract);
        }

        @Override public SolidityParser.BlockContext getBodyContext() { return ctx.block(); }

        @Override public boolean hasOverride(Contract callingContract) {
            return false; // Constructors cannot be overridden
        }

        public boolean isDefaultConstructor() { return this.ctx == null; }
    }

    public static class Modifier extends Callable {
        public SolidityParser.ModifierDefinitionContext ctx;
        public boolean isVirtual;
        public boolean overrides;

        public Modifier(String name, Contract owner) { super(name, owner); }

        @Override public String getDisplayName(Contract callingContract) {
            if (!this.owner.equals(callingContract) && this.hasOverride(callingContract)) {
                return "__" + owner.name + "__" + name;
            } else {
                return name;
            }
        }

        @Override public String getModFreeDisplayName(Contract callingContract) { return name; }

        public String getDisplayName(Contract callingContract, Callable mainCallable,
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

        @Override public SolidityParser.BlockContext getBodyContext() { return ctx.block(); }

        @Override public boolean hasOverride(Contract callingContract) {
            boolean modifierFound = false;
            for (Contract parent : callingContract.c3Linearization) {
                for (Modifier parentModifier : parent.modifiers) {
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

    public static class Variable {
        public String name;
        public String renamedName; // A local variable may be renamed if it is shadowing another local variable.
        public String typename;
        public DataLocation dataLocation = DataLocation.UNSPECIFIED;
        public boolean isConstant; // comes from either 'constant' or 'immutable' keywords

        public Variable(String name, String typename) {
            this.name = this.renamedName = name;
            this.typename = typename;
        }

        public String getJavaDeclaration(Environment env) {
            return solidityToJavaType(typename, env) + " " + renamedName;
        }

        public String getDisplayName(Contract callingContract) { return renamedName; }

        @Override public String toString() {
            return typename + " " + renamedName;
        }
    }

    public static class Field extends Variable {
        public Contract owner;
        public FieldVisibility visibility;
        public SolidityParser.StateVariableDeclarationContext ctx;

        public Field(String name, String typename) { super(name, typename); }

        /**
         * Get the name of the field as it would be displayed from the POV of 'callingContract'.
         * I.e., if the field has been imported from another contract, the display name may contain
         * as a prefix the name of the contract that originally defined the field.
         * @param callingContract The contract in which the field should 'displayed'.
         * @return The display name.
         */
        public String getDisplayName(Contract callingContract) {
			if (this.owner.equals(callingContract)) {
				return name;
			}
			boolean isOutermost = false;
			boolean fieldFound = false;
			Iterator<Solidity.Contract> it = callingContract.c3Linearization.descendingIterator();
			while (it.hasNext() && !fieldFound) {
				Solidity.Contract parent = it.next();
				for (Solidity.Field field : parent.fields) {
					if (field.name.equals(this.name)) {
						isOutermost = field.equals(this);
						fieldFound = true;
						break;
					}
				}
			}
			assert fieldFound == true;
			return isOutermost ? name : "__" + owner.name + "__" + name;
        }

        public boolean hasOverride(Contract callingContract) {
            for (Contract parent : callingContract.c3Linearization) {
                Field parentField = parent.getField(this.name);
                if (parentField != null && !parentField.owner.equals(callingContract)) {
                    return true;
                }
            }
            return false;
        }
    }

    public static class LogicalVariable extends Variable {
        public LogicalVariable(String name, String typename) { super(name, typename); }
    }

    public static class Enum {
        public final String name;
        public final Contract owner;

        public Enum(String name, Contract owner) {
            this.name = name;
            this.owner = owner;
        }

        @Override public String toString() {
            return getDisplayName();
        }

        public String getDisplayName() {
            return owner.name + "." + name;
        }
    }

    public static class Struct {
        public final String name;
        public final Contract owner;
        public final boolean isFree;
        public List<Variable> fields = new LinkedList<>();

        public Struct(String name) {
            this.name = name;
            this.owner = null;
            this.isFree = true;
        }

        public Struct(String name, Contract owner) {
            this.name = name;
            this.owner = owner;
            this.isFree = false;
        }

        @Override public String toString() {
            return getDisplayName();
        }

        public String getDisplayName() {
            return this.isFree ? name : owner.name + "." + name;
        }

        public Variable getVariableWithName(String name) {
            for (Variable var : fields) {
                if (var.name.equals(name)) {
                    return var;
                }
            }
            return null;
        }
    }

    public static class Contract {
        public String name;
        public ContractType type;
        public boolean isAbstract;
        public LinkedList<Contract> c3Linearization = new LinkedList<>(); // List does not have descendingIterator
        public List<Contract> inheritanceList = new LinkedList<>();
        // The below are self-defined functions/fields/constructors, not inherited ones
        public List<Function> functions = new LinkedList<>();
        public List<Field> fields = new LinkedList<>();
        public List<Modifier> modifiers = new LinkedList<>();
        public List<Enum> enums = new LinkedList<>();
        public List<Struct> structs = new LinkedList<>();
        public Constructor constructor;
        // All libraries named 'L' such that the declaration 'using L for *' is found within the contract.
        public List<Contract> globalUsingForLibraries = new LinkedList<>();
        // All library attachments made from Using For statements,
        //  for each type (contract, elementary type, struct), within the contract.
        //  The map is (type => libraries).
        public Map<String, List<Contract>> typeLibAttachments = new HashMap<>();
        public int inputFileStartLine;

        public Map<String, Contract> contractsInInputFile;

        /**
         * Get a list of all fields that are visible in this contract, i.e., all fields in this contract + all
         * non-private fields in this contract's parents.
         * @return A list of all visible fields.
         */
        public List<Field> getAllVisibleInheritedFields() {
            List<Field> fields = new LinkedList<>(this.fields);
            for (Contract parent : c3Linearization) {
                if (parent == this) {
                    continue;
                }
                for (Field field : parent.fields) {
                    if (field.visibility != FieldVisibility.PRIVATE) {
                        fields.add(field);
                    }
                }
            }
            return fields;
        }

        public List<Function> getAllVisibleInheritedFunctions() {
            List<Function> functions = new LinkedList<>(this.functions);
            for (Contract parent : c3Linearization) {
                if (parent == this) {
                    continue;
                }
                for (Function function : parent.functions) {
                    if (function.visibility != FunctionVisibility.PRIVATE) {
                        functions.add(function);
                    }
                }
            }
            return functions;
        }

        public void removeFieldWithIdent(String ident) {
            Iterator<Field> it = fields.iterator();
            while (it.hasNext()) {
                Field field = it.next();
                if (field.name.equals(ident)) {
                    it.remove();
                    break;
                }
            }
        }

        /**
         * Collect all library functions attached to the given type inside this contract, given all its containing
         * "Using For" declarations. The type could be elementary or a contract.
         * @param type The type to check for it.
         * @return A set of all the library functions for the type in this contract.
         */
        public List<Function> getAttachedLibraryFunctionsForType(String type) {
            List<Function> attachedLibFunctions = new LinkedList<>();
            for (Contract lib : globalUsingForLibraries) {
                lib.functions.forEach(libFun -> {
                    if (!attachedLibFunctions.contains(libFun))
                        attachedLibFunctions.add(libFun);
                });
            }
            if (typeLibAttachments.containsKey(type)) {
                for (Contract lib : typeLibAttachments.get(type)) {
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
         * @return If it was found, the function, otherwise null.
         */
        public Function getFunction(String funName,
                                    List<String> argTypes,
                                    Contract callContainingContract,
                                    Environment env,
                                    boolean allowConversions)
        {
            for (Function fun : functions) {
                if (fun.name.equals(funName)) {
                    if (argTypesMatchesFunctionParams(argTypes, fun.getParamTypeNames(), fun,
                            callContainingContract, env, allowConversions)) {
                        return fun;
                    }
                }
            }
            return null;
        }

        public Function getFunction(String funName) {
            for (Function fun : functions) {
                if (fun.name.equals(funName)) {
                    return fun;
                }
            }
            return null;
        }

        public Field getField(String fieldName) {
            for (Field field : fields) {
                if (field.name.equals(fieldName))
                    return field;
            }
            return null;
        }

        public Modifier getModifier(String modName) {
            // Note: modifiers cannot be overloaded with different argument lists.
            for (Modifier mod : modifiers) {
                if (mod.name.equals(modName))
                    return mod;
            }
            return null;
        }

        public Enum getEnum(String enumName) {
            int dotPos = enumName.indexOf(".");
            if (dotPos == -1) {
                for (Enum enum_ : enums) {
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

        public Struct getStruct(String structName) {
            int dotPos = structName.indexOf(".");
            if (dotPos == -1) {
                for (Struct struct : structs) {
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
         * Get the name of the contract before (less derived) the supplied contract in this contract's linearization list.
         * @param contractName The name of the contract that should be after the contract this is returned.
         * @return The contract before the one given by 'contractName', in the linearization list of this coontract.
         */
        public Contract getContractBefore(String contractName) {
            Iterator<Contract> it = c3Linearization.descendingIterator();
            while (it.hasNext()) {
                Contract parent = it.next();
                if (parent.name.equals(contractName)) {
                    if (it.hasNext())
                        return it.next();
                    return null;
                }
            }
            return null;
        }

        public boolean hasDefaultConstructor() {
            return this.constructor.isDefaultConstructor();
        }

        public String getDisplayName() { return getContractDisplayName(name); }
    }

    /**
     * Make a conversion between a Solidity type and a Java type.
     * @param solidityTypeName The name of the type in Solidity
     * @return The name of the type in Java (as it is translated).
     */
    public static String solidityToJavaType(String solidityTypeName, Environment env) {
        if (env != null && env.contracts != null && env.contracts.containsKey(solidityTypeName)) {
            return getContractDisplayName(solidityTypeName);
        }
        if (typeIsInt(solidityTypeName)) {
            return "int";
        }
        if (typeIsBytes(solidityTypeName)) {
            return solidityTypeName.equals("bytes") ? "int[]" : "int";
        }

        // TODO: do more thoroughly
        return switch (solidityTypeName) {
            case "uint", "uint256", "bytes32" -> "int";
            case "bool" -> "boolean";
            case "string" -> "String";
            case "address" -> "Address";
            case "address[]" -> "Address[]";
            case "uint[]" -> "int[]";
            case "uint256[]" -> "int[]";
            case "bytes32[]" -> "int[]";
            case "mapping(address=>uint)" -> "int[]";
            case "mapping(address=>uint256)" -> "int[]";
            case "mapping(uint=>uint)" -> "int[]";
            case "mapping(uint256=>uint256)" -> "int[]";
            case "mapping(uint=>address)" -> "Address[]";
            case "mapping(uint256=>address)" -> "Address[]";
            case "mapping(address=>bool)" -> "boolean[]";
            case "mapping(uint=>bool)" -> "boolean[]";
            case "mapping(uint256=>bool)" -> "boolean[]";
            case "mapping(address=>string)" -> "String[]";
            case "mapping(uint=>string)" -> "String[]";
            case "mapping(uint256=>string)" -> "String[]";
            default -> solidityTypeName;
        };
    }

    public static boolean isValueType(String type) {
        // TODO
        return true;
    }

    public static boolean isReferenceType(String type) { return !isValueType(type); }

    public static boolean implicitTypeConversionIsAllowed(String typeFrom, String typeTo) {
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

    public static boolean typeIsElementary(String type) { return elementarySolidityTypes.contains(type); }

    public static boolean typeIsArray(String type) {
        return type.endsWith("[]") || type.startsWith("bytes") || type.equals("string");
    }

    public static boolean typeIsInt(String type) {
        return (type.startsWith("int") || type.startsWith("uint")) && elementarySolidityTypes.contains(type);
    }

    public static boolean typeIsBytes(String type) {
        return type.startsWith("bytes") && elementarySolidityTypes.contains(type);
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
    public static boolean parameterListsAreEqual(List<String> params1, List<String> params2) {
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
     * @return True if the types align so that the function could be called with the arguments given in the function call.
     */
    public static boolean argTypesMatchesFunctionParams(List<String> callArgTypes,
                                                        List<String> funParamTypes,
                                                        Callable callable,
                                                        Contract callContainingContract,
                                                        Environment env,
                                                        boolean allowConversions)
    {
        if (funParamTypes.size() != callArgTypes.size())
            return false;
        int index = -1;
        for (String argType : callArgTypes) {
            ++index;
            String paramType = funParamTypes.get(index);
            if (!argTypeMatchesFunctionParam(argType, paramType, callable, callContainingContract, env, allowConversions)) {
                return false;
            }
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
    public static boolean argTypeMatchesFunctionParam(String callArgType,
                                                      String funParamType,
                                                      Callable callable,
                                                      Contract callContainingContract,
                                                      Environment env,
                                                      boolean allowConversions)
    {
        if (callArgType.equals(funParamType)) {
            return true;
        }
        if (allowConversions && callContainingContract.contractsInInputFile.containsKey(callArgType) &&
                callContainingContract.contractsInInputFile.containsKey(funParamType)) {
            // Allow for polymorphism; check for subtypes
            Contract contract = callContainingContract.contractsInInputFile.get(callArgType);
            for (Contract parent : contract.c3Linearization) {
                if (parent.name.equals(funParamType)) {
                    return true;
                }
            }
            return false;
        }
        // Check if the types are enums
        Enum enum1 = env.lookupEnum(callArgType, callContainingContract);
        Enum enum2 = env.lookupEnum(funParamType, callable.owner);
        if (enum1 != null && enum2 != null) {
            return enum1.name.equals(enum2.name) && enum1.owner.equals(enum2.owner);
        } else if (enum1 != null || enum2 != null) {
            return false;
        }
        // Check if the types are structs
        Struct struct1 = env.lookupStruct(callArgType, callContainingContract);
        Struct struct2 = env.lookupStruct(funParamType, callable.owner);
        if (struct1 != null && struct2 != null) {
            return struct1.name.equals(struct2.name) && struct1.owner.equals(struct2.owner);
        } else if (struct1 != null || struct2 != null) {
            return false;
        }

        if (allowConversions) {
            return implicitTypeConversionIsAllowed(callArgType, funParamType);
        }
        return false;
    }

    public static String getContractDisplayName(String contractName) {
        return contractName + "Impl";
    }
}
