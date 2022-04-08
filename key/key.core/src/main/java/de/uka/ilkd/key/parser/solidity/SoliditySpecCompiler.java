package de.uka.ilkd.key.parser.solidity;

import java.util.*;

import java.io.File;
import java.io.IOException;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Token;

public class SoliditySpecCompiler {
    private static final String SELF_PLACEHOLDER = "__self__";
    private static final int SPEC_COMMENT_CHANNEL = 2;
    private static final int SPEC_LINE_COMMENT_CHANNEL = 3;

    private final String specContractName;
    private final String specCallableName;
    private final ProofObligations pos = new ProofObligations();

    private Environment env = new Environment();
    private String contractNameInPOs;
    private Solidity.Contract specContract;
    private Solidity.Callable specCallable;

    private void error(String string) throws RuntimeException {
        throw new RuntimeException(string);
    }
    
    public SoliditySpecCompiler(String specContractName, String specCallableName) {
        this.specContractName = specContractName;
        this.specCallableName = specCallableName;
    }

    private String makeKeYFileString() {
        String output = SpecCompilerUtils.loadTemplate(specContract.type);
        output = output.replace(SpecCompilerUtils.INVARIANT_PLACEHOLDER, pos.invariant != null ? pos.invariant : "true")
                       .replace(SpecCompilerUtils.CONTRACT_NAME_PLACEHOLDER,contractNameInPOs)
                       .replace(SpecCompilerUtils.PROGRAM_VARIABLES_PLACEHOLDER, makeProgramVariablesString(specCallable))
                       .replace(SpecCompilerUtils.SCHEMA_VARIABLES_PLACEHOLDER, makeSchemaVariablesString(specCallable))
                       .replace(SpecCompilerUtils.VARCOND_PLACEHOLDER, makeVarcondString(specCallable))
                       .replace(SpecCompilerUtils.ASSUMPTION_PLACEHOLDER, makeAssumptionString(specCallable))
                       .replace(SpecCompilerUtils.HEAP_UPDATE_PLACEHOLDER, makeHeapUpdateString(specCallable))
                       .replace(SpecCompilerUtils.FUNCTION_PLACEHOLDER, makeFunctionCallString(specCallable))
                       .replace(SpecCompilerUtils.POSTCONDITION_PLACEHOLDER, makePostConditionString(specCallable));
        output = output.replaceAll(SELF_PLACEHOLDER, specContract.type == Solidity.ContractType.CONTRACT ? "self" : "caller");
        return output;
    }

    private String makeProgramVariablesString(Solidity.Callable callable) {
        String resultVar;
        if (callable instanceof Solidity.Function) {
            if (callable.returnType.equals("void")) {
                resultVar = "";
            } else {
                resultVar = Solidity.solidityToJavaType(callable.returnType, env) + " _result;\n";
            }
        } else {
            resultVar = "";
        }
        if (callable.params.isEmpty()) {
            return resultVar;
        } else {
            StringBuilder output = new StringBuilder(resultVar);
            for (Solidity.Variable var : callable.params) {
                String javaType = Solidity.solidityToJavaType(var.typename, env);
                output.append(javaType + " " + var.name + ";\n");
                output.append(javaType + " _" + var.name + ";\n");
            }
            return output.toString();
        }
    }

    private String makeSchemaVariablesString(Solidity.Callable callable) {
        StringBuilder output = new StringBuilder();
        for(Map.Entry<String,Solidity.LogicalVariable> e : env.cumulativeLogicalVars.entrySet()) {
            output.append("\\schemaVar \\variable " + Solidity.solidityToJavaType(e.getValue().typename, env) +
                    " " + e.getKey() + ";\n");
        }
        return output.toString();
    }

    private String makeVarcondString(Solidity.Callable callable) {
        StringBuilder output = new StringBuilder();
        for (Map.Entry<String,Solidity.LogicalVariable> e : env.cumulativeLogicalVars.entrySet()) {
            output.append("\\notFreeIn(" + e.getKey() + "," + SpecCompilerUtils.HeapType.HEAP_H + "," + SELF_PLACEHOLDER + "),");
        }
        if (output.length() > 0) {
            output.deleteCharAt(output.length()-1);
        } else {
           return "";
        }
        return "\\varcond(" + output + ")";
    }

    private String makeAssumptionString(Solidity.Callable callable) {
        StringBuilder output = new StringBuilder();
        if (!(callable instanceof Solidity.Constructor) && specContract.type == Solidity.ContractType.CONTRACT) {
            output.append("&\nCInv(heap," + SELF_PLACEHOLDER + ") ");
        }
        if (callable.isPayable) {
            output.append("&\nmsg.value >= 0 ");
        } else {
            output.append("&\nmsg.value = 0 ");
        }
        // Let all contract-fields be non-null
        List<Solidity.Field> visibleFields = specContract.getAllVisibleInheritedFields();
        for (Solidity.Field field : visibleFields) {
            output.append("&\n" + SELF_PLACEHOLDER + "." + field.name + " != null " );
        }
        // Let all function arguments be non-null
        for (Solidity.Variable param : callable.params) {
            output.append("&\n" + param.name + " != null ");
        }
        if (pos.posMap.get(callable.name).assumes != null) {
            output.append("&\n" + pos.posMap.get(callable.name).assumes + " ");
        }
        if (callable instanceof Solidity.Constructor) {
            output.append("&\nmsg.sender != " + SELF_PLACEHOLDER + " ");
            output.append("&\n(\\forall Address a; int::select(heap,net,address(a))=0) ");
            // Assumptions for state variable values
            // This is very hard-coded. Sorry.
            for (Solidity.Field field : specContract.getAllVisibleInheritedFields()) {
                String javaType = Solidity.solidityToJavaType(field.typename, env);
                if (javaType.equals("boolean[]")) {
                    output.append("&\n(\\forall int i; " + SELF_PLACEHOLDER + "." + field.name + "[i] = FALSE) ");
                } else if (javaType.equals("int[]")) {
                    output.append("&\n(\\forall int i; " + SELF_PLACEHOLDER + "." + field.name+ "[i] = 0) ");
                } else if (javaType.equals("Address[]")) {
                    output.append("&\nint::select(heap," + SELF_PLACEHOLDER + "." + field.name + ",arr_length) = 0 ");
                }
            }
        }
        return output.toString();
    }

    private String makeHeapUpdateString(Solidity.Callable callable) {
        StringBuilder parString = new StringBuilder();
        for (Solidity.Variable var : callable.params) {
            parString.append(" || _" + var.name + " := " + var.name);
        }

        String mapping = pos.isGross(callable.name) ? "gross_from" : "net";
        return callable.isPayable ?
            ( (callable instanceof Solidity.Constructor) ?
            parString + "|| heap:=store(heap," + mapping + ", address(msg.sender),msg.value)" :
            parString + "|| heap:=store(heap, " + mapping + ", address(msg.sender), int::select(heap, " + mapping + ", address(msg.sender)) + msg.value)"
            ) :
            parString.toString();
    }

    private String makeFunctionCallString(Solidity.Callable callable) {
        StringBuilder parString = new StringBuilder();
        for (Solidity.Variable var : callable.params) {
            parString.append(",_" + var.name);
        }
        String assignment;
        if (callable instanceof Solidity.Function) {
            if (callable.returnType.equals("void")) {
                assignment = "";
            } else {
                assignment = "_result = ";
            }
        } else {
            assignment = "";
        }
        String shownCallableName;
        if (callable instanceof Solidity.Constructor) {
            shownCallableName = "<init>";
        } else {
            shownCallableName = callable.name;
        }
        return assignment + "" + SELF_PLACEHOLDER + "." + shownCallableName + "(msg" + parString + ")@" + contractNameInPOs + ";";
    }

    private String makePostConditionString(Solidity.Callable callable) {
        StringBuilder ret = new StringBuilder();
        if (specContract.type == Solidity.ContractType.CONTRACT) {
            ret.append("CInv(heap," + SELF_PLACEHOLDER + ")\n");
        } 
        // only_if:s
        if (pos.posMap.get(callable.name).onlyIf != null) {
            ret.append(" & " + pos.posMap.get(callable.name).onlyIf);
        }
        // on_success
        if (pos.posMap.get(callable.name).onSuccess != null) {
            ret.append(" & " + pos.posMap.get(callable.name).onSuccess);
        }
        //assignable stuff
        if (!(callable instanceof Solidity.Constructor)) {
            String elementOfString = "";
            List<String> objFields = pos.posMap.get(callable.name).assignable;
            if (objFields.size() > 0) {
                int listSize = objFields.size();
                StringBuilder output = new StringBuilder();
                int i=0;
                for (String s : objFields) {
                    if (i++ < listSize-1) {
                        output.append("union(");
                        output.append("singleton(" + s + "),");
                    } else {
                        output.append("singleton(" + s + ")");
        
                    }
                }
                for (i=0; i<listSize-1; i++) {
                    output.append(')');
                }
                elementOfString = "elementOf(o,f," + output + ") | ";
                elementOfString = SpecCompilerUtils.injectHeap(SpecCompilerUtils.HeapType.OLD_HEAP, elementOfString);
            }
            ret.append("& (\\forall Field f; \\forall java.lang.Object o; (" + elementOfString +
                    " !o = null & !o.<created>@savedHeap = TRUE | o.f = o.f@savedHeap))");
        }
        String retStr = ret.toString();
        if (specContract.type != Solidity.ContractType.CONTRACT) {
            retStr = retStr.replaceFirst("&","");
        }
        return retStr;
    }

    private Solidity.Callable callableFromLineNo(int line) {
        Solidity.Callable currentCallable = null;
        int currentCallableLineNo = line;
        for (Solidity.Function function : specContract.getAllVisibleInheritedFunctions()) {
            if (function.inputFileStartLine > line &&
                    (currentCallableLineNo == line || function.inputFileStartLine < currentCallableLineNo)) {
                currentCallable = function;
                currentCallableLineNo = function.inputFileStartLine;
            }
        }
        if (specContract.hasNonDefaultConstructor()) {
            if (specContract.constructor.inputFileStartLine > line &&
                    (currentCallableLineNo == line || specContract.constructor.inputFileStartLine < currentCallableLineNo)) {
                currentCallable = specContract.constructor;
            }
        }
        return currentCallable;
    }


    private boolean specIsInContract(int startLine) {
        if (startLine < specContract.inputFileStartLine) {
            return false;
        }
        int maxLine = 0;
        for (Solidity.Function function : specContract.functions) {
            if (function.inputFileStartLine > maxLine) {
                maxLine = function.inputFileStartLine;
            }
        }
        if (specContract.hasNonDefaultConstructor() && specContract.constructor.inputFileStartLine > maxLine) {
            maxLine = specContract.constructor.inputFileStartLine;
        }
        return startLine >= specContract.inputFileStartLine && startLine <= maxLine;
    }

    public void collectProofObligations(String fileName) throws IOException {
        // First pass (reads Solidity code and collects contracts and names)
        {
            SolidityPreVisitor preVisitor = new SolidityPreVisitor();
            SolidityLexer lexer = new SolidityLexer(CharStreams.fromStream(new File(fileName).toURI().toURL().openStream()));
            SolidityParser parser = new SolidityParser(new CommonTokenStream(lexer));
            SolidityParser.SourceUnitContext solidityAST = parser.sourceUnit();
            env = preVisitor.visitSourceUnit(solidityAST);

            specContract = env.contracts.get(specContractName);
            if (specContract == null) {
                error("Could not find contract/interface/library " + specContractName);
            }
            // TODO: currently, this just gets the first function that it finds (it does not consider overloads)
            if (specCallableName.equals(specContractName)) { // constructor
                specCallable = specContract.constructor;
            } else { // function
                specCallable = specContract.getFunction(specCallableName);
            }
            if (specCallable == null) {
                error("Could not find function " + specCallableName + " in contract " + specContractName);
            }
            contractNameInPOs = specContract.type == Solidity.ContractType.CONTRACT ? specContract.getDisplayName() : specContractName;

            specContract.fields.add(new Solidity.Field("balance", "int"));
            env.addLogicalVar("all_addresses", "address");
        }
        // Second pass (reads specification)
        {
            CharStream c = CharStreams.fromStream(new File(fileName).toURI().toURL().openStream());
            SolidityLexer lexer = new SolidityLexer(c);
            Token t;
            while ((t = lexer.nextToken()).getType() != Token.EOF) {
                if ((t.getChannel() == SPEC_COMMENT_CHANNEL || t.getChannel() == SPEC_LINE_COMMENT_CHANNEL)) {
                    String toParse = t.getChannel() == SPEC_COMMENT_CHANNEL ?
                            t.getText().substring(SPEC_LINE_COMMENT_CHANNEL,t.getText().length()-2) : t.getText().substring(SPEC_LINE_COMMENT_CHANNEL);
                    SolidityParser parser = new SolidityParser(
                            new CommonTokenStream(new SolidityLexer(CharStreams.fromString(toParse,"dummy"))));
                    SolidityParser.SpecDefinitionContext solidityAST = parser.specDefinition();
                    Solidity.Callable callable = callableFromLineNo(t.getLine());
                    // If this spec is not in the contract to verify, only look for library invariants
                    boolean onlyLibraryInvariant = !specIsInContract(t.getLine());
                    SoliditySpecVisitor visitor = new SoliditySpecVisitor(contractNameInPOs, callable,
                            specContract, env, pos, onlyLibraryInvariant);
                    visitor.visit(solidityAST);
                }
            }
        }
    }

    public static void main(String[] args) throws IOException {
        SoliditySpecCompiler ssc = new SoliditySpecCompiler(args[1], args[2]);
        ssc.collectProofObligations(args[0]);
        System.out.println(ssc.makeKeYFileString());
    }
}