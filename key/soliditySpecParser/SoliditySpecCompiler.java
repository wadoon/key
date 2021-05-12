import java.util.*;

import java.io.File;
import java.io.IOException;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Token;

public class SoliditySpecCompiler {
    private final String SELF_PLACEHOLDER = "__self__";

    private ProofObligations pos = new ProofObligations();
    private String contractName;
    private String functionName;
    private String contractNameInPOs;
    private int contractStartLine;
    private Environment env;
    
    public SoliditySpecCompiler(String contractName, String functionName) {
        this.contractName = contractName;
        this.functionName = functionName;
        this.contractNameInPOs = "contractNameInPOs NOT SET";
    }

    private String makeKeYFileString() {
        String function = functionName;
        if (!env.funcs.containsKey(function)) {
            throw new IllegalArgumentException("Could not find function " + function);
        }
        boolean funcPayable = env.funcs.get(function).payable;
        boolean forConstructor = function.equals(contractName);
        String output = SpecCompilerUtils.loadTemplate(env.unitType);
        output = output.replace(SpecCompilerUtils.INVARIANT_PLACEHOLDER, pos.invariant != null ? pos.invariant : "true")
                       .replace(SpecCompilerUtils.CONTRACT_NAME_PLACEHOLDER,contractNameInPOs)
                       .replace(SpecCompilerUtils.PROGRAM_VARIABLES_PLACEHOLDER, makeProgramVariablesString(function))
                       .replace(SpecCompilerUtils.SCHEMA_VARIABLES_PLACEHOLDER, makeSchemaVariablesString())
                       .replace(SpecCompilerUtils.VARCOND_PLACEHOLDER, makeVarcondString())
                       .replace(SpecCompilerUtils.ASSUMPTION_PLACEHOLDER, makeAssumptionString(function, funcPayable, forConstructor))
                       .replace(SpecCompilerUtils.HEAP_UPDATE_PLACEHOLDER, makeHeapUpdateString(function, funcPayable, forConstructor))
                       .replace(SpecCompilerUtils.FUNCTION_PLACEHOLDER, makeFunctionCallString(function,forConstructor))
                       .replace(SpecCompilerUtils.POSTCONDITION_PLACEHOLDER, makePostConditionString(function,forConstructor));
        output = output.replaceAll(SELF_PLACEHOLDER, env.unitType == Environment.UnitType.CONTRACT ? "self" : "caller");
        return output;
    }

    private String makeProgramVariablesString(String func) {
        String resultVar = env.funcs.get(func).returnType != null ?
            env.funcs.get(func).returnType + " _result;\n" : "";
        Map<String,String> parameters = env.funcs.get(func).parameters;
        if (parameters.size() == 0) {
            return resultVar;
        } else {
            StringBuilder sb = new StringBuilder(resultVar);
            for (Map.Entry<String,String> e : parameters.entrySet()) {
                sb.append(e.getValue() + " " + e.getKey() + ";\n");
                sb.append(e.getValue() + " _" + e.getKey() + ";\n");
            }
            return sb.toString();
        }
    }

    private String makeSchemaVariablesString() {
        StringBuilder sb = new StringBuilder();
        for(Map.Entry<String,String> e : env.cumulativeLogicalVars.entrySet()) {
            sb.append("\\schemaVar \\variable " + e.getValue() + " " + e.getKey() + ";\n");
        }
        return sb.toString();
    }

    private String makeVarcondString() {
        StringBuilder sb = new StringBuilder();
        for (Map.Entry<String,String> e : env.cumulativeLogicalVars.entrySet()) {
            sb.append("\\notFreeIn(" + e.getKey() + "," + SpecCompilerUtils.HeapType.HEAP_H.toString() + "," + SELF_PLACEHOLDER + "),");
        }
        if (sb.length() > 0) {
            sb.deleteCharAt(sb.length()-1);
        } else {
           return "";
        }
        return "\\varcond(" + sb.toString() + ")";
    }

    private String makeAssumptionString(String func, boolean payable, boolean forConstructor) {
        StringBuilder sb = new StringBuilder();
        if (!forConstructor && env.unitType == Environment.UnitType.CONTRACT) {
            sb.append("&\nCInv(heap," + SELF_PLACEHOLDER + ") ");
        }
        if (payable) {
            sb.append("&\nmsg.value >= 0 ");
        } else {
            sb.append("&\nmsg.value = 0 ");
        }
        for (String var : env.vars.keySet()) {
            if (!(("Message").equals(env.vars.get(var)) || ("logical").equals(env.vars.get(var)) 
                    || ("this").equals(var))) {
                sb.append("&\n" + SELF_PLACEHOLDER + "." + var + "!= null " );
            }
        }
        if (pos.posMap.get(func).assumes != null) {
            sb.append("&\n" + pos.posMap.get(func).assumes + " ");
        }
        if (forConstructor) {
            sb.append("&\nmsg.sender != " + SELF_PLACEHOLDER + " ");
            sb.append("&\n(\\forall Address a; int::select(heap,net,address(a))=0) ");
            // Assumptions for state variable values
            // This is very hard-coded. Sorry.
            for (Map.Entry<String,String> p : env.vars.entrySet()) {
                if (!(("enum").equals(p.getValue()) || ("Message").equals(env.vars.get(p.getValue())))) {
                    if (("boolean[]").equals(p.getValue())) {
                        // bool array (mappings)
                        sb.append("&\n(\\forall int i; " + SELF_PLACEHOLDER + "." + p.getKey() + "[i] = FALSE) ");
                    } else if (("int[]").equals(p.getValue())) {
                        // int array (mappings)
                        sb.append("&\n(\\forall int i; " + SELF_PLACEHOLDER + "." + p.getKey() + "[i] = 0) ");
                    } else if (("Address[]").equals(p.getValue())) {
                        // address array (really array)
                        // arrName.arr_length = 0
                        sb.append("&\nint::select(heap," + SELF_PLACEHOLDER + "." + p.getKey() + ",arr_length) = 0 ");
                    }
                    // enums
                    // save default value during first pass
                }
            }
        }
        return sb.toString();
    }

    private String makeHeapUpdateString(String func, boolean payable, boolean forConstructor) {
        String parString = "";
        for (String p : env.funcs.get(func).parameterOrder) {
            parString = parString + " || _" + p + " := " + p;
        }

        String mapping = pos.isGross(func) ? "gross_from" : "net";
        return payable ?
            ( forConstructor ? 
            parString + "|| heap:=store(heap," + mapping + ", address(msg.sender),msg.value)" :
            parString + "|| heap:=store(heap, " + mapping + ", address(msg.sender), int::select(heap, " + mapping + ", address(msg.sender)) + msg.value)"
            ) :
            parString;
    }

    private String makeFunctionCallString(String func, boolean forConstructor) {
        List<String> parameters = env.funcs.get(func).parameterOrder;
        String parString = "";
        for (String p : parameters) {
            parString = parString + ",_" + p;
        }
        String assignment = env.funcs.get(func).returnType != null ? "_result = " : "";
        if (forConstructor) {
            func = "<init>";
        }
        return assignment + "" + SELF_PLACEHOLDER + "." + func + "(msg" + parString + ")@" + contractNameInPOs + ";";
    }

    private String makePostConditionString(String func, boolean forConstructor) {
        String ret = "";
        if (env.unitType == Environment.UnitType.CONTRACT) {
            ret = "CInv(heap," + SELF_PLACEHOLDER + ")\n";
        } 
        // only_if:s
        if (pos.posMap.get(func).onlyIf != null) {
            ret = ret + " & " + pos.posMap.get(func).onlyIf;
        }
        // on_success
        if (pos.posMap.get(func).onSuccess != null) {
            ret = ret + " & " + pos.posMap.get(func).onSuccess;
        }
        //assignable stuff
        if (!forConstructor) { 
            String elementOfString = "";
            List<String> objFields = pos.posMap.get(func).assignable;
            if (objFields != null) {
                int listSize = objFields.size();
                StringBuilder sb = new StringBuilder();
                int i=0;
                for (String s : objFields) {
                    if (i++ < listSize-1) {
                        sb.append("union(");
                        sb.append("singleton(" + s + "),");
                    } else {
                        sb.append("singleton(" + s + ")");
        
                    }
                }
                for (i=0; i<listSize-1; i++) {
                    sb.append(')');
                }
                elementOfString = "elementOf(o,f," + sb.toString() + ") | ";
                elementOfString = SpecCompilerUtils.injectHeap(SpecCompilerUtils.HeapType.OLD_HEAP, elementOfString);
            }
            ret = ret + "& (\\forall Field f; \\forall java.lang.Object o; (" + elementOfString +
                    " !o = null & !o.<created>@savedHeap = TRUE | o.f = o.f@savedHeap))";
        }
        if (env.unitType != Environment.UnitType.CONTRACT) {
            ret = ret.replaceFirst("&","");
        }
        return ret; 
    }

    private String functionFromLineNo(int line) {
        String currentFunction = null;
        int currentFunctionLineNo = line;
        for (Map.Entry<String,Environment.FunctionInfo> e: env.funcs.entrySet()) {
            if (e.getValue().lineNo > line && 
                        (currentFunctionLineNo == line || e.getValue().lineNo < currentFunctionLineNo)) {
                currentFunction = e.getKey();
                currentFunctionLineNo = e.getValue().lineNo;
            }
        }
        return currentFunction;
    }

    private boolean specIsInContract(int startLine) {
        if (startLine < contractStartLine) {
            return false;
        }
        int maxLine = 0;
        for (Map.Entry<String,Environment.FunctionInfo> e: env.funcs.entrySet()) {
            if (e.getValue().lineNo > maxLine) {
                maxLine = e.getValue().lineNo;
            }
        }
        return startLine >= contractStartLine && startLine <= maxLine;
    }

    public void collectProofObligations(String fileName) throws IOException {

        // first pass (reads Solidity code)
        SoliditySpecPreVisitor sspv = new SoliditySpecPreVisitor(contractName, functionName);
        sspv.parse(fileName);
        env = sspv.getEnvironment();
        contractStartLine = sspv.getContractStartLine();
        contractNameInPOs = env.unitType == Environment.UnitType.CONTRACT ? contractName + "Impl" : contractName;
        if (env.unitType == Environment.UnitType.INTERFACE) {
            throw new UnsupportedOperationException("Interfaces not yet supported.");
        }

//System.out.println(env.vars);

        // second pass (reads specification)
        CharStream c = CharStreams.fromStream(new File(fileName).toURI().toURL().openStream());
        SolidityLexer lexer = new SolidityLexer(c);
        Token t = null;
        while ((t = lexer.nextToken()).getType() != Token.EOF) {
            if (t.getChannel() == 2 || t.getChannel() == 3) {
                String toParse = t.getChannel() == 2 ?
                        t.getText().substring(3,t.getText().length()-2) : t.getText().substring(3);
                SolidityParser parser = new SolidityParser(
                    new CommonTokenStream(new SolidityLexer(CharStreams.fromString(toParse,"dummy"))));
                SolidityParser.SpecDefinitionContext solidityAST = parser.specDefinition();
                if (specIsInContract(t.getLine())) {
                    String function = functionFromLineNo(t.getLine());
                    SoliditySpecVisitor visitor = new SoliditySpecVisitor(contractNameInPOs, function, env, pos);
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
