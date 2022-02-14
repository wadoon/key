package de.uka.ilkd.key.parser.solidity;

import org.abego.treelayout.internal.util.Contract;
import org.antlr.v4.runtime.tree.TerminalNode;

import de.uka.ilkd.key.parser.solidity.SolidityParser.ConstructorDefinitionContext;
import de.uka.ilkd.key.parser.solidity.SolidityParser.ContractDefinitionContext;
import de.uka.ilkd.key.parser.solidity.SolidityParser.InheritanceSpecifierContext;

import java.util.*;
import java.util.regex.*;

public class SolidityTranslationVisitor extends SolidityBaseVisitor<String> {
	// Generated from key.core/src/main/antlr/de/uka/ilkd/key/parser/Solidity.g4 by ANTLR 4.7.1

	private enum ContractVisibility {
		EXTERNAL, PUBLIC, INTERNAL, PRIVATE
	}

	private class FunctionInfo {
		public ContractVisibility visibility;
		public boolean isVirtual;
		public boolean overrides;
		public boolean isStatic;
		public String name;
		public String header;
		public String bodyWithSuperCalls; // includes the outermost {}. super calls have not been replaced.

		public String getOutputWithSuperCalls() {
			return header + bodyWithSuperCalls;
		}
	}

    private class ContractInfo {
        // contract types
        public static final int UNDEFINED = 0;
        public static final int CONTRACT = 1;
        public static final int INTERFACE = 2;
        public static final int LIBRARY = 3;

        // maps are { identifier => output string}
		Map<String,FunctionInfo> functions = new HashMap<>();
        Map<String,String> variables = new HashMap<>();
        Map<String,String> enums = new HashMap<>();

        List<String> constructorHeaders = new LinkedList<>();
        List<String> is = new LinkedList<>();
        int type;
        String name;
		boolean isAbstract; // TODO

		/*
        public String toString() {
            return constructorHeaders + "\n" +
            functionHeaders + "\n" +
            variables + "\n" +
            enums + "\n" +
            is + "\n" +
            name + "\n" + 
            type + "\n";
        }

		 */
    }

    private Map<String,ContractInfo> contractMap = new HashMap<>();
    private ContractInfo currentContractInfo;
	private String currentFunction; // The function currently being visited, or the last one.
	private HashMap<String, LinkedList<String>> c3Linearizations = new HashMap<>();
	public String output = "";

	/* A super call, e.g., super.foo() */
	private Pattern superCallPattern = Pattern.compile("[\\{\\};][\s\t\n]*super\\.");
	/* A function call to an internally defined function, e.g., foo() */
	private Pattern javaInternalFunctionCallPattern = Pattern.compile("[^\\w_\\.][\\w_]+\\(");
	/* A function call to an externally defined function, e.g., contractA.foo() */
	private Pattern javaExternalFunctionCallPattern = Pattern.compile("[^\\w_\\.][\\w_]+\\.[\\w_]+\\(");

	/**
	 * Replaces all super calls -- super.foo() -- with calls '__C__foo()', where C is a concrete, parent contract
	 * to 'derivingContract'. 'derivingContract' is the contract implementing the contract containing within 'output'.
	 * However, 'originalContract' may have inherited this contract', and 'baseContract'
	 * is then the parent contract originally implementing the function.
	 * @param derivingContract The deriving contract.
	 * @param baseContract The base contract implementing the functions that are to be treated.
	 * @param output The original function output.
	 * @return The identifier of the function as it will exist inside 'derivingContract', e.g., __C__foo.
	 */
	private String replaceSuperCallsInFunction(String derivingContract, String baseContract, String output) {
		// Find super calls
		Matcher superCallMatcher = superCallPattern.matcher(output);
		int matcherStartIndex = 0;
		while (superCallMatcher.find(matcherStartIndex)) {
			int superEndIndex = superCallMatcher.end();
			// Find which function is called: super.___(
			int functionEndIndex = output.indexOf('(', superEndIndex);
			String function = output.substring(superEndIndex, functionEndIndex);
			// Construct the explicit call. The output will be __C__function, where C is some parent contract
			String explicitCall = replaceSuperCall(derivingContract, baseContract, function);
			// Replace the super call with the explicit call.
			output = output.substring(0, superEndIndex - 6 /* 6 == length of "super." */) +
					explicitCall + output.substring(functionEndIndex);
			matcherStartIndex = functionEndIndex;
		}
		return output;
	}

	/**
	 * Replaces a super call -- super.foo() -- with a call '__C__foo()', where C is a concrete, parent contract
	 * to 'derivingContract'. 'derivingContract' is the contract implementing 'outsideFunction'.
	 * However, this is a flattened contract, and 'parentContract' is the parent contract originally
	 * implementing the function.
	 * @param derivingContract The contract in which the super call takes place.
	 * @param baseContract The contract that originally implemented the function, that 'derivingContract' inherited.
	 * @param function The function identifier.
	 * @return The identifier of the function as it will exist inside 'derivingContract', e.g., __C__foo.
	 */
	private String replaceSuperCall(String derivingContract, String baseContract, String function) {
		ContractInfo contractInfo = contractMap.get(derivingContract);
		if (contractInfo == null)
			error("Fatal: cannot find original contract when replacing super call.");

		LinkedList<String> linearization = c3Linearizations.get(derivingContract);
		if (linearization == null)
			error("Fatal: the currently inspected contract does not have a linearization.");

		// Find the most derived parent in the contract's linearization list that contains the function ('functionCalled')
		// The parent has to be more derived than 'parentContract', as this is the original owner of the inherited function,
		// before the contract flattening took place.
		Iterator<String> it = linearization.descendingIterator();
		it.next(); // Skip the last element (it is the contract itself)
		boolean functionFound = false;
		boolean baseContractFound = false;
		String parentContractWithFunction = null;
		if (derivingContract.equals(baseContract))
			baseContractFound = true;

		while (it.hasNext()) {
			String parentContract = it.next();
			if (!baseContractFound) {
				if (baseContract.equals(parentContract)) {
					baseContractFound = true;
				}
				continue;
			}
			ContractInfo parentContractInfo = contractMap.get(parentContract);
			boolean hasFunction = parentContractInfo.functions.get(function) != null;
			if (hasFunction) {
				functionFound = true;
				parentContractWithFunction = parentContract;
				break;
			}
		}
		if (!baseContractFound) {
			error("Could not replace super call to " + function + " inside of " +
					derivingContract + "; original implementer of " +
					function + " could not be found.");
		}
		if (functionFound) {
			return constructMangledInheritedFunctionName(parentContractWithFunction, function);
		} else {
			error("Contract " + derivingContract + " has a super call to " +
					function + ", but no parent of " + derivingContract +
					" implements function " + function + ".");
		}
		return null;
	}

	/**
	 * Construct a mangled name for inherited functions.
	 * @param baseContract The contract that the function was inherited from.
	 * @param function The function identifier.
	 * @return A mangled function identifier.
	 */
	private String constructMangledInheritedFunctionName(String baseContract, String function) {
		return "__" + baseContract + "__" + function;
	}

	/**
	 * In contract 'originalContract', replaces all internal and external calls to inherited functions
	 * with their mangled versions, within the function whose output is in 'functionOutput'.
	 * @param originalContract The contract inheriting the function whose output is 'functionOutput'.
	 * @param baseContract The contract originally implementing the function whose output is 'functionOutput'.
	 * @param functionOutput The old function output.
	 * @return
	 */
	private String renameInheritedFunctions(String originalContract, String baseContract, String functionOutput) {
		// Replace all internal calls, such as "foo()", with explicit calls "__C__foo()",
		// where C is 'baseContract' which 'originalContract' inherited the function from.
		Matcher internalCallMatcher = javaInternalFunctionCallPattern.matcher(functionOutput);
		while (internalCallMatcher.find()) {
			int funNameStartPos = internalCallMatcher.start() + 1;
			int funNameEndPos = internalCallMatcher.end() - 1;
			String funName = functionOutput.substring(funNameStartPos, funNameEndPos);
			String newName = constructMangledInheritedFunctionName(baseContract, funName);
			functionOutput = functionOutput.replaceFirst(funName, newName);
		}
		// Replace all external calls, such as "C.foo()", which new, explicit calls "__C__foo()".
		// If 'C' is 'super', replace it with a concrete contract.
		Matcher externalCallMatcher = javaExternalFunctionCallPattern.matcher(functionOutput);
		while (externalCallMatcher.find()) {
			int fullFunCallStartPos = externalCallMatcher.start() + 1;
			int fullFunCallEndPos = externalCallMatcher.end() - 1;
			int dotPos = functionOutput.indexOf('.', fullFunCallStartPos);
			String fullFunCall = functionOutput.substring(fullFunCallStartPos, fullFunCallEndPos);
			String contractName = functionOutput.substring(fullFunCallStartPos, dotPos);
			String funName = functionOutput.substring(dotPos + 1, fullFunCallEndPos);

			String newFunCall;
			if (contractName.equals("super"))
				newFunCall = replaceSuperCall(originalContract, baseContract, funName);
			else
				newFunCall = constructMangledInheritedFunctionName(baseContract, funName);
			functionOutput = functionOutput.replaceFirst(fullFunCall, newFunCall);
		}
		return functionOutput;
	}

	/**
	 * Perform 'flattening'; add all functions from 'contract''s parents into 'contract' itself.
	 * Super calls are also replaced with explicit calls.
	 * @param contract
	 * @return The new output for 'contract', but with inherit functions added.
	 */
	private String addInheritedFunctionsToContractOutput(String contract) {
		// TODO: Skip unimplemented functions from interfaces/abstract classes.
		final StringBuffer inheritedContractsOutputBuffer = new StringBuffer();
		LinkedList<String> c3Linearization = c3Linearizations.get(contract);
		Iterator<String> it = c3Linearization.descendingIterator();
		it.next(); // Skip the last contract; it is the contract itself
		while (it.hasNext()) {
			String baseContract = it.next();
			ContractInfo baseContractInfo = contractMap.get(baseContract);
			if (baseContractInfo == null) {
				error("Fatal: could not find the base contract " + baseContract +
						" in the linearization for contract " + contract);
			}
			// Add all inherited functions from contract 'baseContract'
			Map<String, FunctionInfo> baseFunctions = baseContractInfo.functions;
			for (String function : baseFunctions.keySet()) {
				// Construct a new function header, containing a mangled function name
				FunctionInfo functionInfo = baseFunctions.get(function);
				String newFunctionName = constructMangledInheritedFunctionName(baseContract, function);
				String newHeader = functionInfo.header.replaceFirst(function, newFunctionName);
				// In the body, replace all super calls with explicit calls, and non-super calls with calls to mangled functions.
				String newBody = String.valueOf(functionInfo.bodyWithSuperCalls);
				newBody = renameInheritedFunctions(contract, baseContract, newBody);
				// Add to the output.
				inheritedContractsOutputBuffer.append(newHeader + newBody + '\n');
			}
		}

		String inheritedContractsOutput = inheritedContractsOutputBuffer.toString();

		return inheritedContractsOutput;
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

	/**
	 * Constructs the C3 linearization for 'contract', which is a list of contracts that the contract
	 * inherits from, from least derived to most derived, including the contract itself at the end.
	 * In other words, it is a flattening of the contract's inheritance tree structure.
	 * @param contract
	 * @return The contract's C3 linearization as a list of contracts, from least derived to most derived.
	 */
	private LinkedList<String> constructC3Linearization(String contract) {
		ContractInfo contractInfo = contractMap.get(contract);
		// If the inheritance list is empty, the linearization is just the contract itself.
		if (contractInfo.is.isEmpty()) {
			return new LinkedList<String>(Collections.singleton(contract));
		} else {
			// Construct the list of lists that is to be sent to the 'merge' function.
			// It contains the linearizations of all contracts in the inheritance list + the inheritance list itself.
			LinkedList<LinkedList<String>> baseLinearizations = new LinkedList<>();
			for (String base : contractInfo.is) {
				if (base.equals(contract)) {
					error("A contract may not inherit from itself.");
				}
				LinkedList<String> baseLinearization = c3Linearizations.get(base);
				if (baseLinearization == null) {
					error("The contract inherits from something not defined yet");
				}
				// Create a copy so that, when 'baseLinearizations' is mutated by merge(), 'linearizations' is not mutated.
				baseLinearizations.addFirst(new LinkedList<>(baseLinearization));
			}
			// Copy the inheritance list, put the contract at the end of it, and put it in the merge input list
			LinkedList<String> inheritanceList = new LinkedList<>(contractInfo.is);
			inheritanceList.addLast(contract);
			baseLinearizations.addLast(inheritanceList);
			// Perform the 'merge' operation to get the actual linearization.
			LinkedList<LinkedList<String>> toMerge = new LinkedList<>(baseLinearizations);
			LinkedList<String> linearization = merge(toMerge);
			if (linearization == null) {
				error("Linearization failed.");
			}
			return linearization;
		}
	}

	/**
	 * Constructs a Java interface for the contract that is currently being visited.
	 * This interface contains declarations for all functions that the contract introduces (not overrides),
	 * and the resulting Java class for the contract shall 'implement' this interface.
	 * The interface 'extends' all the corresponding interfaces for the contracts in the contract's inheritance list.
	 * @return
	 */
	private String makeInterface() {
		StringBuilder sb = new StringBuilder();
		sb.append("interface " + currentContractInfo.name);

		// build 'extends' list
		if (currentContractInfo.is.size() > 0) {
			sb.append(" extends");
			currentContractInfo.is.forEach(c -> {
				sb.append(" " + c + ",");
			});
			sb.deleteCharAt(sb.length()-1);
		}
		sb.append(" {\n");

		// add own functions, but only if they were introduced in this contract (they don't override)
		for (FunctionInfo functionInfo : currentContractInfo.functions.values()) {
			if (!functionInfo.overrides)
				sb.append(functionInfo.header + ";\n");
		}

		sb.append("}\n");
		return sb.toString();
	}


	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitSourceUnit(SolidityParser.SourceUnitContext ctx) { 
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
        currentContractInfo = new ContractInfo();
        currentContractInfo.name = ctx.identifier().getText();
		String contractName = currentContractInfo.name;
        // TODO parse type
        currentContractInfo.type = ContractInfo.UNDEFINED;
		if (ctx.ContractKeyword() != null) {
            currentContractInfo.type = ContractInfo.CONTRACT;
        } else if (ctx.InterfaceKeyword() != null) {
            currentContractInfo.type = ContractInfo.INTERFACE;
        } else if (ctx.LibraryKeyword() != null) {
            currentContractInfo.type = ContractInfo.LIBRARY;
        } else {
			error("No valid contract type found for contract " + contractName);
		}
        contractMap.put(contractName, currentContractInfo);

		StringBuffer inheritanceList = new StringBuffer();

		for (InheritanceSpecifierContext ictx : ctx.inheritanceSpecifier()) {
            currentContractInfo.is.add(ictx.getText());
			inheritanceList.append(ictx.getText());		
			inheritanceList.append(",");
		}
		if (ctx.inheritanceSpecifier().size() > 0) {
			inheritanceList.setCharAt(inheritanceList.length()-1,' ');
		}

		// Construct the C3 linearization for the contract.
		// NOTE: this should be done before the children of the contract definition are visited,
		// because they may make use of the linearization.
		LinkedList<String> c3Linearization = constructC3Linearization(contractName);
		if (c3Linearization == null)
			error("Could not construct the C3 linearization for contract " + contractName);
		c3Linearizations.put(contractName, c3Linearization);

		// Create a class/interface from the contract and visit each of its children
        final StringBuffer contract = new StringBuffer();
        if (currentContractInfo.type == ContractInfo.CONTRACT) {
            contract.append("class " + contractName + "Impl extends Address implements " + contractName + " {\n");
   		    ctx.contractPart().stream().forEach(part -> contract.append(visit(part) + "\n"));
        } else if (currentContractInfo.type == ContractInfo.INTERFACE) {
            contract.append("interface " + contractName);
            if (currentContractInfo.is.size() > 0) {
				contract.append(" extends");
                currentContractInfo.is.forEach(c -> contract.append(" " + c + ","));
                contract.setCharAt(contract.length()-1,' ');
            }
            contract.append(" {\n");
   		    ctx.contractPart().stream().forEach(part -> contract.append(visit(part) + ";\n"));
        } else if (currentContractInfo.type == ContractInfo.LIBRARY) {
            contract.append("class " + contractName + " {\n");
   		    ctx.contractPart().stream().forEach(part -> contract.append(visit(part) + "\n"));
        }

		// Put all implemented functions from the contract's parents inside this one.
		// This also replaces all super calls that are found within those functions.
		String inheritedContractsOutput = addInheritedFunctionsToContractOutput(contractName);

		contract.append(inheritedContractsOutput);

		// TODO: put all constructors from the contract's parents inside this one, as private functions.

        if (currentContractInfo.type == ContractInfo.CONTRACT) {
            output += makeInterface();
        } 
        output += contract.append("}\n").toString();

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
		String output = "  ";
		if ( !ctx.PublicKeyword().isEmpty()) {
			output += "public";
		} else if (!ctx.InternalKeyword().isEmpty()) {
			output += "protected /* internal */";
		} else if (!ctx.PrivateKeyword().isEmpty()) {
			output += "private";
		} else if (!ctx.ConstantKeyword().isEmpty()) {
			output += "final";
		}
		output += " ";
		output += convertType(ctx.typeName().getText());
		output += " ";
		output += ctx.identifier().getText();
		if (ctx.expression() != null && !ctx.expression().isEmpty()) {
			output += " = " + visit(ctx.expression());
		}
        currentContractInfo.variables.put(ctx.identifier().getText(), output);
		return output + ";"; 
	}

	private String convertType(String text) {
		String typeName = text.replace(" ", "");
		switch (text) {
		case "uint": case "uint256": case "bytes32": 
			typeName = "int";break;
		case "bool"    : typeName = "boolean";break;
		case "address" : typeName = "Address";break;
		case "address[]" : typeName = "Address[]";break;
		case "uint[]" : typeName = "int[]";break;
		case "uint256[]" : typeName = "int[]";break;
		case "bytes32[]" : typeName = "int[]";break;
		case "mapping(address=>uint)": typeName="int[]";break;
		case "mapping(address=>uint256)": typeName="int[]";break;
		case "mapping(uint=>uint)": typeName="int[]";break;
		case "mapping(uint256=>uint256)": typeName="int[]";break;
		case "mapping(uint=>address)": typeName="Address[]";break;
		case "mapping(uint256=>address)": typeName="Address[]";break;
		case "mapping(address=>bool)": typeName="boolean[]";break;
		case "mapping(uint=>bool)": typeName="boolean[]";break;
		case "mapping(uint256=>bool)": typeName="boolean[]";break;
		default: break;		
		}

		return typeName;
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
		StringBuffer structDef = new StringBuffer("static class "+visit(ctx.identifier()) + "{\n");
		ctx.variableDeclaration().stream().forEach(v -> structDef.append(visit(v)).append(";\n"));
		structDef.append("}");
		return structDef.toString(); 
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitConstructorDefinition(SolidityParser.ConstructorDefinitionContext ctx) { 
		String modifier = "";
		if (!ctx.modifierList().PublicKeyword().isEmpty()) {
			modifier = "public";
		} else if (!ctx.modifierList().PrivateKeyword().isEmpty()) {
			modifier = "private";			
		}

		// TODO user defined modifiers

		StringBuffer parameters = new StringBuffer("Message msg,");
		ctx.parameterList().parameter().stream().forEach(param -> 
		parameters.append(visit(param) + ","));
		if (parameters.length() > 0) { 
			parameters.deleteCharAt(parameters.length() - 1);
		}

		StringBuffer mods = new StringBuffer();

		ctx.modifierList().modifierInvocation().stream().
		forEach(inv -> mods.append(visit(inv) + ";\n"));

		StringBuffer body = new StringBuffer(visit(ctx.block()));
		if (mods.length() > 0) body.insert(body.indexOf("{") + 1, "\n" + mods);

        currentContractInfo.constructorHeaders.add(modifier + " void " + currentContractInfo.name + "Impl(" + parameters + ")" );
		return modifier + " " + currentContractInfo.name + "Impl(" + parameters + ")" + body;
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitModifierDefinition(SolidityParser.ModifierDefinitionContext ctx) { 
		String modName = ctx.identifier() == null ? "fallback" : visit(ctx.identifier());
		String modifier = "private";

		StringBuffer parameters = new StringBuffer("Message msg,");
		if (ctx.parameterList() != null) {
			ctx.parameterList().parameter().stream().forEach(param -> 
				parameters.append(visit(param) + ","));
		}
		if (parameters.length() > 0) parameters.deleteCharAt(parameters.length() - 1);
		String returnType = ctx.getParent() instanceof ConstructorDefinitionContext ? "" : "void";
		return modifier + " " + returnType + " " + modName + "(" + parameters + ")" + visit(ctx.block());
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitModifierInvocation(SolidityParser.ModifierInvocationContext ctx) { 
		String modName = visit(ctx.identifier());
        // hack: if "modifier" is really a parent constructor
        if (currentContractInfo.is.contains(modName)) {
            modName += "Impl";
        }

		StringBuffer arguments = new StringBuffer("msg");

		if (ctx.expressionList() != null && !ctx.expressionList().isEmpty()) {			
			ctx.expressionList().expression().stream()
			.forEach(elt -> arguments.append("," + visit(elt)));
		}

		return modName + "(" + arguments + ")";
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>The default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	@Override public String visitFunctionDefinition(SolidityParser.FunctionDefinitionContext ctx) { 
		String fctName = ctx.identifier() == null ? "fallback" : visit(ctx.identifier());
		String modifier = "";
		if (!ctx.modifierList().PublicKeyword().isEmpty()) {
			modifier = "public";
		} else if (!ctx.modifierList().PrivateKeyword().isEmpty()) {
			modifier = "private";
		}

		currentFunction = fctName;

		FunctionInfo functionInfo = new FunctionInfo();
		functionInfo.isVirtual = !ctx.modifierList().VirtualKeyword().isEmpty();
		functionInfo.overrides = !ctx.modifierList().OverrideKeyword().isEmpty();
		if (!ctx.modifierList().PublicKeyword().isEmpty()) {
			functionInfo.visibility = ContractVisibility.PUBLIC;
		} else if (!ctx.modifierList().ExternalKeyword().isEmpty()) {
			functionInfo.visibility = ContractVisibility.EXTERNAL;
		} else if (!ctx.modifierList().InternalKeyword().isEmpty()) {
			functionInfo.visibility = ContractVisibility.INTERNAL;
		} else if (!ctx.modifierList().PrivateKeyword().isEmpty()) {
			functionInfo.visibility = ContractVisibility.PRIVATE;
		} else {
			error("No visibility specifier found for function " + fctName +
					" in contract " + currentContractInfo.name);
		}

		// If the function overrides, make sure that there is a virtual function in the contract's inheritance tree.
		if (functionInfo.overrides) {
			boolean baseFunctionFound = false;
			LinkedList<String> linearization = c3Linearizations.get(currentContractInfo.name);
			for (String baseClass : linearization) {
				if (baseClass.equals(currentContractInfo.name))
					continue;
				FunctionInfo baseClassFunctionInfo = contractMap.get(baseClass).functions.get(fctName);
				if (baseClassFunctionInfo != null && baseClassFunctionInfo.isVirtual) {
					baseFunctionFound = true;
					break;
				}
			}
			if (!baseFunctionFound) {
				error("Contract " + currentContractInfo.name +
						" overrides non-existent function " + fctName);
			}
		}

		// TODO user defined modifiers

		StringBuffer parameters;
		
		switch(fctName) {
		case "require":case "assert": 
			parameters = new StringBuffer();
			break;
		default: parameters = new StringBuffer("Message msg,");		
		}
		
		ctx.parameterList().parameter().stream().forEach(param -> 
			parameters.append(visit(param) + ","));

		if (parameters.length() > 0) parameters.deleteCharAt(parameters.length() - 1);

		String returnType = ctx.getParent() instanceof ConstructorDefinitionContext ? "" : "void";

		if (ctx.returnParameters() != null && !ctx.returnParameters().isEmpty()) {
			returnType = visit(ctx.returnParameters().parameterList().parameter(0).typeName());	
		}

		StringBuffer mods = new StringBuffer();

		ctx.modifierList().modifierInvocation().stream().
		forEach(inv -> mods.append(visit(inv) + ";\n"));
        
        StringBuffer body = new StringBuffer();
        if (ctx.block() != null) {
    		body = new StringBuffer(visit(ctx.block()));
    		if (mods.length() > 0) body.insert(body.indexOf("{") + 1, "\n" + mods);
        }

        String fctHeader = modifier + (currentContractInfo.type == ContractInfo.LIBRARY ? " static " : " ") 
            + returnType + " " + fctName + "(" + parameters + ")";

		// Have two versions of the function body: one with super calls,
		// and one where the super calls have been replaced with explicit functions
		functionInfo.bodyWithSuperCalls = body.toString();
		functionInfo.header = fctHeader;
		currentContractInfo.functions.put(fctName, functionInfo);

		String bodyWithoutSuperCalls = replaceSuperCallsInFunction(
				currentContractInfo.name, currentContractInfo.name, String.valueOf(functionInfo.bodyWithSuperCalls));

		return fctHeader + " " + bodyWithoutSuperCalls;
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
		StringBuffer enumDef = new StringBuffer("enum ");
		enumDef.append(visit(ctx.identifier()));
		enumDef.append("{");
		ctx.enumValue().stream().forEach(v -> enumDef.append(visit(v.identifier())+","));		
		enumDef.deleteCharAt(enumDef.length()-1);
		enumDef.append("}");
        currentContractInfo.enums.put(ctx.identifier().getText(),enumDef.toString());
		return enumDef.toString(); 
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
		return visit(ctx.typeName()) + " " + visit(ctx.identifier()); 
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
		return visit(ctx.typeName()) + " " + visit(ctx.identifier()); 
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

		ctx.statement().stream().forEach(stmnt -> output.append("\n" + visit(stmnt)));

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
		String decl = this.visit(ctx.variableDeclaration());
		if (ctx.variableDeclaration() != null) { // If it is a declaration of one variable...
			if (ctx.expression() != null){
				decl = decl + "=" + this.visit(ctx.expression());
			}
			return decl+";";
		}
		else { // If it is a list of identifiers...
			// TODO
		}
		return "//"+ctx.getText();	
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
        String comparableName = fctName;

        // handle calls to member functions, and super calls
		boolean isSuperCall = false;
        int dotPos = fctName.lastIndexOf('.');
        if (dotPos != -1) {
            comparableName = fctName.substring(dotPos+1);
			if (fctName.substring(0, dotPos).equals("super"))
				isSuperCall = true;
        }
		if (isSuperCall) {
			// Replace the super call with a call to an explicit function
			//fctName = replaceSuperCall(currentContractInfo.name, currentContractInfo.name, currentFunction, comparableName);
		}

		StringBuffer arguments;
        boolean skip = false;
		switch(comparableName) {
        case "require2":
            arguments = new StringBuffer("(int)sender != 0,");
            fctName = "require";
            skip = true;
            break;
        case "require3":
            arguments = new StringBuffer("(int)recipient != 0,");
            fctName = "require";
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

		return fctName + "(" + arguments + ")";
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
        // if this is an explicit call to derived contract's function
        if (contractMap.containsKey(exp) && contractMap.get(exp).type != ContractInfo.LIBRARY) {
            return "__" + exp + "__" + ident;
        }
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
	@Override public String visitNewTypeNameExpression(SolidityParser.NewTypeNameExpressionContext ctx) { return visitChildren(ctx); }
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
	@Override public String visitExpressionList(SolidityParser.ExpressionListContext ctx) { return visitChildren(ctx); }
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
		return ctx.getText(); 
	}

	@Override public String visitTerminal(TerminalNode n) {
		return "// " + n.getText();

	}

	public String getOutput() {
		return output;
	}

}
