import java.util.*;

import java.io.File;
import java.io.IOException;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Token;

public class SoliditySpecCompiler {
    private String invariant;
    private Map<String,FunctionProofObligations> posMap = new HashMap<>();

    private String contractName;
    private String contractNameInPOs;
    private int contractStartLine;
    private Environment env;
    
    public SoliditySpecCompiler(String contractName) {
        this.contractName = contractName;
        contractNameInPOs = contractName + "Impl";
    }

    private String makeKeYFileString(String function) {
        if (!env.funcs.containsKey(function)) {
            throw new IllegalArgumentException("Could not find function " + function);
        }
        boolean funcPayable = env.funcs.get(function).payable;
        boolean forConstructor = function.equals(contractName);
        String output = SpecCompilerUtils.loadTemplate();
        output = output.replace(SpecCompilerUtils.INVARIANT_PLACEHOLDER, invariant != null ? invariant : "true")
                       .replace(SpecCompilerUtils.CONTRACT_NAME_PLACEHOLDER,contractNameInPOs)
                       .replace(SpecCompilerUtils.PROGRAM_VARIABLES_PLACEHOLDER, makeProgramVariablesString(function))
                       .replace(SpecCompilerUtils.SCHEMA_VARIABLES_PLACEHOLDER, makeSchemaVariablesString())
                       .replace(SpecCompilerUtils.VARCOND_PLACEHOLDER, makeVarcondString())
                       .replace(SpecCompilerUtils.ASSUMPTION_PLACEHOLDER, makeAssumptionString(funcPayable,forConstructor))
                       .replace(SpecCompilerUtils.HEAP_UPDATE_PLACEHOLDER, makeHeapUpdateString(function, funcPayable, forConstructor))
                       .replace(SpecCompilerUtils.FUNCTION_PLACEHOLDER, makeFunctionCallString(function,forConstructor))
                       .replace(SpecCompilerUtils.POSTCONDITION_PLACEHOLDER, makePostConditionString(function,forConstructor));
        return output;
    }

    private String makeProgramVariablesString(String func) {
        Map<String,String> parameters = env.funcs.get(func).parameters;
        if (parameters.size() == 0) {
            return "";
        } else {
            StringBuilder sb = new StringBuilder();
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
            sb.append("\\notFreeIn(" + e.getKey() + "," + SpecCompilerUtils.HeapType.HEAP_H.toString() + ",self),");
        }
        if (sb.length() > 0) {
            sb.deleteCharAt(sb.length()-1);
        } else {
           return "";
        }
        return "\\varcond(" + sb.toString() + ")";
    }

    private String makeAssumptionString(boolean payable, boolean forConstructor) {
        StringBuilder sb = new StringBuilder();
        if (!forConstructor) {
            sb.append("&\nCInv(heap,self) ");
        }
        if (payable) {
            sb.append("&\nmsg.value >= 0 ");
        } else {
            sb.append("&\nmsg.value = 0 ");
        }
        for (String var : env.vars.keySet()) {
            if (!(("Message").equals(env.vars.get(var)) || ("logical").equals(env.vars.get(var)) 
                    || ("this").equals(var))) {
                sb.append("&\nself." + var + "!= null " );
            }
        }
        if (forConstructor) {
            sb.append("&\n(\\forall Address a; int::select(heap,net,address(a))=0) ");
            // assumptions for state variable values
            for (Map.Entry<String,String> p : env.vars.entrySet()) {
                if (!(("enum").equals(p.getValue()) || ("Message").equals(env.vars.get(p.getValue())))) {
                    if (("boolean[]").equals(p.getValue())) {
                        // bool array (mappings)
                        sb.append("&\n(\\forall int i; self." + p.getKey() + "[i] = FALSE) ");
                    } else if (("int[]").equals(p.getValue())) {
                        // int array (mappings)
                        sb.append("&\n(\\forall int i; self." + p.getKey() + "[i] = 0) ");
                    } else if (("Address[]").equals(p.getValue())) {
                        // address array (really array)
                        // arrName.arr_length = 0
                        sb.append("&\nint::select(heap,self." + p.getKey() + ",arr_length) = 0 ");
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

        String mapping = posMap.get(func).isGross ? "gross_from" : "net";
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
        if (forConstructor) {
            func = "<init>";
        }
        return "self." + func + "(msg" + parString + ")@" + contractNameInPOs + ";";
    }

    private String makePostConditionString(String func, boolean forConstructor) {
        String ret = "";
        // only_if:s
        if (posMap.get(func).onlyIf != null) {
            ret = " & " + posMap.get(func).onlyIf;
        }
        // on_success
        if (posMap.get(func).onSuccess != null) {
            ret = ret + " & " + posMap.get(func).onSuccess;
        }
        //assignable stuff
        if (!forConstructor) { 
            String elementOfString = "";
            List<String> objFields = posMap.get(func).assignable;
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
        SoliditySpecPreVisitor sspv = new SoliditySpecPreVisitor(contractName);
        sspv.parse(fileName);
        env = sspv.getEnvironment();
        contractStartLine = sspv.getContractStartLine();

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
                    SoliditySpecVisitor visitor = new SoliditySpecVisitor(contractNameInPOs, function, env);
                    visitor.visit(solidityAST);
                    if (visitor.invariant != null) {
                        invariant = visitor.invariant;
                    } else {
                        posMap.put(function, visitor.pos);
                    }
                }
            }
        }
    }

    public static void main(String[] args) throws IOException {
        SoliditySpecCompiler ssc = new SoliditySpecCompiler(args[1]);
        ssc.collectProofObligations(args[0]);
        System.out.println(ssc.makeKeYFileString(args[2]));
    }

}
