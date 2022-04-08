package de.uka.ilkd.key.parser.solidity;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.io.File;
import java.net.URI;
import java.util.*;

/* This visitor is used to collect all the contracts and their functions/fields/modifiers/constructors that
   are within the input file, before the bodies of these are actually visited fully for some other purpose, e.g.,
   to produce the Java text output for the source file, or for a specification.
   This is so that, e.g., if a function calls another function that is defined after the former function,
   that function can know that the latter function exists.
   In addition, we also construct C3 linearizations of the inheritance hierarchy within the input file.
*/
public class SolidityPreVisitor extends SolidityBaseVisitor<Environment> {
    private final Environment env = new Environment();
    private boolean currentlyVisitingContract = false;
    private Solidity.Contract currentContract;
    private Solidity.Callable currentCallable;

    private void error(String string) throws RuntimeException {
        throw new RuntimeException(string);
    }
    
    @Override
    public Environment visitSourceUnit(SolidityParser.SourceUnitContext ctx) {
        ctx.importDirective().forEach(this::visit);
        ctx.structDefinition().forEach(this::visit); // free structs
        ctx.contractDefinition().forEach(this::visit);
        return env;
    }

    @Override
    public Environment visitImportDirective(SolidityParser.ImportDirectiveContext ctx) {
        // Open the file specified by the import directive. For now, the file path given should be absolute.
        // Parse the given file, and visit the AST to produce a list of contracts contained therein.
        // The textual output is not needed. Merge the imported contract list with the current one.
        String absoluteFilePath = ctx.StringLiteral().getText();
        absoluteFilePath = absoluteFilePath.substring(1, absoluteFilePath.length() - 1);
        SolidityLexer lexer = null;
        try {
            URI solidityLocation = new File(absoluteFilePath).toURI();
            lexer = new SolidityLexer(CharStreams.fromStream(solidityLocation.toURL().openStream()));
        } catch (Exception e) {
            error(e.toString());
        }
        SolidityParser parser = new SolidityParser(new CommonTokenStream(lexer));
        SolidityPreVisitor visitor = new SolidityPreVisitor();
        SolidityParser.SourceUnitContext solidityAST = parser.sourceUnit();
        Environment environment = visitor.visit(solidityAST);
        // If a contract/function/etc shows up multiple times, this is due to circular imports. But Solidity allows this.
        environment.contracts.values().forEach(contract -> {
            if (!env.contracts.containsKey(contract.name)) {
                env.contracts.put(contract.name, contract);
            }
        });
        environment.freeStructs.forEach(newStruct -> {
            // Again, we may run into duplicate structs, which is fine.
            boolean structIsDuplicate = false;
            for (Solidity.Struct struct : env.freeStructs) {
                if (struct.name.equals(newStruct.name)) {
                    structIsDuplicate = true;
                    break;
                }
            }
            if (!structIsDuplicate) {
                env.freeStructs.add(newStruct);
            }
        });
        return env;
    }

    @Override
    public Environment visitContractDefinition(SolidityParser.ContractDefinitionContext ctx) {
        currentlyVisitingContract = true;

        String contractName = ctx.identifier().getText();
        if (env.contracts.containsKey(contractName)) {
            error("Contract redefinition; there exists multiple definitions of the contract " + contractName);
        }
        Solidity.Contract contract = new Solidity.Contract();
        currentContract = contract;
        env.contracts.put(contractName, contract);
        contract.name = contractName;
        contract.inputFileStartLine = ctx.start.getLine();
        contract.contractsInInputFile = env.contracts;
        contract.isAbstract = ctx.AbstractKeyword() != null;
        if (ctx.ContractKeyword() != null) {
            contract.type = Solidity.ContractType.CONTRACT;
        } else if (ctx.InterfaceKeyword() != null) {
            contract.type = Solidity.ContractType.INTERFACE;
        } else if (ctx.LibraryKeyword() != null) {
            contract.type = Solidity.ContractType.LIBRARY;
        } else {
            error("No valid contract type found for contract " + contractName);
        }

        for (SolidityParser.InheritanceSpecifierContext ictx : ctx.inheritanceSpecifier()) {
            String parentName = ictx.getText();
            Solidity.Contract parent = env.contracts.get(parentName);
            if (parent == null) {
                error("Could not locate parent contract " + parentName + " as a parent to contract " +
                        contractName + "; maybe it has not been defined yet?");
            }
            contract.inheritanceList.add(parent);
        }
        constructC3Linearization(contract);
        if (contract.c3Linearization == null)
            error("Could not construct the C3 linearization for contract " + contractName);

        ctx.contractPart().forEach(this::visit);

        // If a constructor was not defined, make a default one.
        if (contract.constructor == null) {
            contract.constructor = new Solidity.Constructor(contract);
            contract.constructor.params = new LinkedList<>();
            // TODO: construct a new SolidityParser.ConstructorDefinitionContext, and add to the constructor?
        }

        currentlyVisitingContract = false;

        return env;
    }

    @Override
    public Environment visitFunctionDefinition(SolidityParser.FunctionDefinitionContext ctx) {
        if (!currentlyVisitingContract) {
            error("Free functions are not supported.");
        }
        String fctName = ctx.identifier() == null ? "fallback" : ctx.identifier().getText();
        Solidity.Function function = new Solidity.Function(fctName, currentContract);
        currentContract.functions.add(function);
        currentCallable = function;
        function.ctx = ctx;
        function.name = fctName;
        function.inputFileStartLine = ctx.start.getLine();

        // TODO: currently, if the function has several return variables,
        //  the function return type is set to the type of the first return variable.
        function.returnType = ctx.getParent() instanceof SolidityParser.ConstructorDefinitionContext ? "" : "void";
        function.returnVars = new LinkedList<>();
        if (ctx.returnParameters() != null && !ctx.returnParameters().isEmpty()) {
            SolidityParser.ParameterContext firstParam = ctx.returnParameters().parameterList().parameter(0);
            function.returnType = firstParam.typeName().getText();
            function.returnVarDataLocation = firstParam.storageLocation() == null ? Solidity.DataLocation.UNSPECIFIED :
                    Solidity.DataLocation.stringToLocation(firstParam.storageLocation().getText());
            ctx.returnParameters().parameterList().parameter().forEach(param -> {
                // Add only named variables. TODO: add unnamed as well?
                if (param.identifier() != null) {
                    function.returnVars.add(
                            new Solidity.Variable(param.identifier().getText(), param.typeName().getText()));
                }
            });
        }

        function.isLibraryFunction = currentContract.type == Solidity.ContractType.LIBRARY;
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
            function.visibility = Solidity.FunctionVisibility.PUBLIC;
        } else if (!ctx.modifierList().ExternalKeyword().isEmpty()) {
            function.visibility = Solidity.FunctionVisibility.EXTERNAL;
        } else if (!ctx.modifierList().InternalKeyword().isEmpty()) {
            function.visibility = Solidity.FunctionVisibility.INTERNAL;
        } else if (!ctx.modifierList().PrivateKeyword().isEmpty()) {
            function.visibility = Solidity.FunctionVisibility.PRIVATE;
        } else {
            error("No visibility specifier found for function " + fctName +
                    " in contract " + currentContract.name);
        }
        ctx.parameterList().parameter().forEach(this::visit);

        return env;
    }

    @Override
    public Environment visitModifierDefinition(SolidityParser.ModifierDefinitionContext ctx) {
        String modName = ctx.identifier() == null ? "fallback" : ctx.identifier().getText();
        Solidity.Modifier modifier = new Solidity.Modifier(modName, currentContract);
        currentContract.modifiers.add(modifier);
        currentCallable = modifier;
        modifier.ctx = ctx;
        modifier.isPayable = false;
        modifier.isVirtual = ctx.VirtualKeyword() != null;
        modifier.overrides = ctx.OverrideKeyword() != null;
        modifier.inputFileStartLine = ctx.start.getLine();
        if (ctx.parameterList() != null && !ctx.parameterList().parameter().isEmpty()) {
            ctx.parameterList().parameter().forEach(this::visit);
        }
        // Note: modifiers' visibility cannot be specified (they are always private).
        return env;
    }

    @Override
    public Environment visitStateVariableDeclaration(SolidityParser.StateVariableDeclarationContext ctx) {
        Solidity.Field field = new Solidity.Field(ctx.identifier().getText(), ctx.typeName().getText());
        field.ctx = ctx;
        field.owner = currentContract;
        field.dataLocation = Solidity.DataLocation.STORAGE;
        field.isConstant = ctx.ConstantKeyword().isEmpty() || ctx.ImmutableKeyword().isEmpty();
        currentContract.fields.add(field);

        if (!ctx.PublicKeyword().isEmpty()) {
            field.visibility = Solidity.FieldVisibility.PUBLIC;
        } else if (!ctx.InternalKeyword().isEmpty()) {
            field.visibility = Solidity.FieldVisibility.INTERNAL;
        } else if (!ctx.PrivateKeyword().isEmpty()) {
            field.visibility = Solidity.FieldVisibility.PRIVATE;
        } else { // The default visibility is "internal"
            field.visibility = Solidity.FieldVisibility.INTERNAL;
        }

        return env;
    }

    @Override
    public Environment visitConstructorDefinition(SolidityParser.ConstructorDefinitionContext ctx) {
        if (currentContract.constructor != null) {
            error("Cannot define more than one constructor for contract " + currentContract.name);
        }
        Solidity.Constructor constructor = new Solidity.Constructor(currentContract);
        currentCallable = currentContract.constructor = constructor;
        constructor.ctx = ctx;
        constructor.inputFileStartLine = ctx.start.getLine();
        ctx.modifierList().stateMutability().forEach(term -> {
            if (term.PayableKeyword() != null) {
                constructor.isPayable = true;
            }
        });
        if (ctx.parameterList() != null && !ctx.parameterList().parameter().isEmpty()) {
            ctx.parameterList().parameter().forEach(this::visit);
        }
        return env;
    }

    @Override
    public Environment visitParameter(SolidityParser.ParameterContext ctx) {
        // Note: in Solidity, unnamed function parameters allowed.
        // For now, we disallow such parameters, for otherwise, the output Java program may become nonsensical.
        if (ctx.identifier() == null) {
            error("SolidiKeY disallows unnamed parameters. See callable '" + currentCallable.name + "';");
        }
        Solidity.Variable var = new Solidity.Variable(ctx.identifier().getText(), ctx.typeName().getText());
        var.dataLocation = ctx.storageLocation() == null ? Solidity.DataLocation.UNSPECIFIED :
                Solidity.DataLocation.stringToLocation(ctx.storageLocation().getText());
        currentCallable.params.add(var);
        return env;
    }

    @Override
    public Environment visitEnumDefinition(SolidityParser.EnumDefinitionContext ctx) {
        if (!currentlyVisitingContract) {
            error("Free enums are not supported.");
        }
        Solidity.Enum enum_ = new Solidity.Enum(ctx.identifier().getText(), currentContract);
        currentContract.enums.add(enum_);
        return env;
    }

    @Override
    public Environment visitStructDefinition(SolidityParser.StructDefinitionContext ctx) {
        Solidity.Struct struct;
        if (currentlyVisitingContract) {
            struct = new Solidity.Struct(ctx.identifier().getText(), currentContract);
            currentContract.structs.add(struct);
        } else {
            struct = new Solidity.Struct(ctx.identifier().getText());
            env.freeStructs.add(struct);
        }
        if (ctx.variableDeclaration() != null) {
            ctx.variableDeclaration().forEach(varCtx -> {
                Solidity.Variable var = new Solidity.Variable(varCtx.identifier().getText(), varCtx.typeName().getText());
                var.dataLocation = Solidity.DataLocation.STORAGE;
                struct.fields.add(var);
            });
        }
        return env;
    }

    @Override
    public Environment visitUsingForDeclaration(SolidityParser.UsingForDeclarationContext ctx) {
        // Seemingly, this statement may only appear at contract scope. If it doesn't, the Solidity program
        // would not compile, and we take it as undefined behaviour.
        String libName = ctx.identifier().getText();
        Solidity.Contract lib = env.contracts.get(libName);
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
        return env;
    }

    /**
     * Constructs the C3 linearization for 'contract', which is a list of contracts that the contract
     * inherits from, from least derived to most derived, including the contract itself at the end.
     * In other words, it is a flattening of the contract's inheritance tree structure.
     * @param contract The contract whose linearization is to be constructed.
     */
    private void constructC3Linearization(Solidity.Contract contract) {
        // If the inheritance list is empty, the linearization is just the contract itself.
        if (contract.inheritanceList.isEmpty()) {
            contract.c3Linearization = new LinkedList<>(Collections.singleton(contract));
        } else {
            // Construct the list of lists that is to be sent to the 'merge' function.
            // It contains the linearizations of all contracts in the inheritance list + the inheritance list itself.
            LinkedList<LinkedList<Solidity.Contract>> baseLinearizations = new LinkedList<>();
            for (Solidity.Contract base : contract.inheritanceList) {
                if (base.equals(contract)) {
                    error("A contract may not inherit from itself.");
                }
                LinkedList<Solidity.Contract> baseLinearization = base.c3Linearization;
                // Create a copy so that, when 'baseLinearizations' is mutated by merge(), 'linearizations' is not mutated.
                baseLinearizations.addFirst(new LinkedList<>(baseLinearization));
            }
            // Copy the inheritance list, put the contract at the end of it, and put it in the merge input list
            LinkedList<Solidity.Contract> inheritanceList = new LinkedList<>(contract.inheritanceList);
            inheritanceList.addLast(contract);
            baseLinearizations.addLast(inheritanceList);
            // Perform the 'merge' operation to get the actual linearization.
            LinkedList<LinkedList<Solidity.Contract>> toMerge = new LinkedList<>(baseLinearizations);
            contract.c3Linearization = merge(toMerge);
        }
    }

    /**
     * See the function 'constructC3Linearization'.
     * Performs the 'merge' step for the list of inheritance lists 'toMerge', as part of the C3 linearization.
     * @param toMerge A list of inheritance lists for a contract, created from its inheritance tree.
     * @return A C3 linearization for the contract corresponding to what is in 'toMerge'.
     */
    private LinkedList<Solidity.Contract> merge(LinkedList<LinkedList<Solidity.Contract>> toMerge) {
        LinkedList<Solidity.Contract> linearization = new LinkedList<>();
        while (!toMerge.isEmpty()) {
            boolean candidateFound = false;
            Solidity.Contract candidate = null;
            // Try to find a candidate by inspecting the head of all lists
            for (LinkedList<Solidity.Contract> baseList : toMerge) {
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
                Iterator<LinkedList<Solidity.Contract>> it = toMerge.iterator();
                while (it.hasNext()) {
                    LinkedList<Solidity.Contract> baseList = it.next();
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
     * @return True if 'candidate' appears only at the end of all lists, false otherwise.
     */
    private boolean candidateAppearsOnlyAtEnd(Solidity.Contract candidate, LinkedList<LinkedList<Solidity.Contract>> lists) {
        for (LinkedList<Solidity.Contract> list : lists) {
            int candidatePos = list.indexOf(candidate);
            if (candidatePos != -1 && candidatePos < list.size() - 1) {
                return false;
            }
        }
        return true;
    }
}