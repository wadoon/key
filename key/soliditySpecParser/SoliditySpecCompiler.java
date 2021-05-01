import java.util.*;

import java.io.File;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Token;

public class SoliditySpecCompiler {
    private static final String CONTRACT_NAME_PLACEHOLDER = "__contract_name_placeholder__";
    private static final String PROGRAM_VARIABLES_PLACEHOLDER = "__program_variables_placeholder__";
    private static final String SCHEMA_VARIABLES_PLACEHOLDER = "__schema_variables_placeholder__";
    private static final String INVARIANT_PLACEHOLDER = "__invariant_placeholder__";
    private static final String ASSUMPTION_PLACEHOLDER = "__assumption_placeholder__";
    private static final String FUNCTION_PLACEHOLDER = "__function_placeholder__";
    private static final String POSTCONDITION_PLACEHOLDER = "__postcondition_placeholder__";
    private static final String VARCOND_PLACEHOLDER = "__varcond_placeholder__";
    private static final String HEAP_UPDATE_PLACEHOLDER = "__heap_update_placeholder__";

    private String invariant;
    private Map<String,FunctionProofObligations> posMap = new HashMap<>();

    private String contractName;
    private Environment env;
    
    public static void main(String[] args) throws IOException {
        SoliditySpecCompiler ssc = new SoliditySpecCompiler();

        // first pass (reads Solidity code)
        SoliditySpecPreVisitor sspv = new SoliditySpecPreVisitor();
        sspv.parse(args[0]);
        ssc.contractName = sspv.contractName;
        ssc.env = sspv.env;
        // second pass (reads specification)
        CharStream c = CharStreams.fromStream(new File(args[0]).toURI().toURL().openStream());
        SolidityLexer lexer = new SolidityLexer(c);
        Token t = null;
        while ((t = lexer.nextToken()).getType() != Token.EOF) {
            if (t.getChannel() == 2 || t.getChannel() == 3) {
                String toParse = t.getChannel() == 2 ? t.getText().substring(3,t.getText().length()-2) : t.getText().substring(3);
                SolidityParser parser = new SolidityParser(new CommonTokenStream(new SolidityLexer(CharStreams.fromString(toParse,"dummy"))));
                SolidityParser.SpecDefinitionContext solidityAST = parser.specDefinition();
                String function = ssc.functionFromLineNo(t.getLine());
                SoliditySpecVisitor visitor = new SoliditySpecVisitor(ssc.contractName, function, ssc.env);
                visitor.visit(solidityAST);
                if (visitor.invariant != null) {
                    ssc.invariant = visitor.invariant;
                } else {
                    ssc.posMap.put(function, visitor.pos);
                }
            }
        }
        String funcName = args[1];
        if (!ssc.env.funcs.containsKey(funcName)) {
            System.out.println("Could not find function " + funcName);
            System.exit(-1);
        }
        boolean funcPayable = ssc.env.funcs.get(funcName).payable;
        boolean forConstructor = funcName.equals(ssc.contractName);
        String output = loadTemplate();
        output = output.replace(INVARIANT_PLACEHOLDER, ssc.invariant != null ? ssc.invariant : "true")
                       .replace(CONTRACT_NAME_PLACEHOLDER,ssc.contractName)
                       .replace(PROGRAM_VARIABLES_PLACEHOLDER, ssc.makeProgramVariables(funcName))
                       .replace(SCHEMA_VARIABLES_PLACEHOLDER, ssc.makeSchemaVariables())
                       .replace(VARCOND_PLACEHOLDER, ssc.makeVarcond())
                       .replace(ASSUMPTION_PLACEHOLDER, ssc.makeAssumption(funcPayable,forConstructor))
                       .replace(HEAP_UPDATE_PLACEHOLDER, ssc.makeHeapUpdate(funcName, funcPayable, forConstructor))
                       .replace(FUNCTION_PLACEHOLDER, ssc.makeFunctionCall(funcName,forConstructor))
                       .replace(POSTCONDITION_PLACEHOLDER, ssc.makePostCondition(funcName,forConstructor));
        System.out.println(output);
    }

    private static String loadTemplate() {
        try {
            return Files.readString(Path.of("include/template.key"));
        } catch (IOException e) {
            e.printStackTrace();
            return "error";
        }
    }

    private String makeProgramVariables(String func) {
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

    private String makeSchemaVariables() {
        StringBuilder sb = new StringBuilder();
        for(Map.Entry<String,String> e : env.cumulativeLogicalVars.entrySet()) {
            sb.append("\\schemaVar \\variable " + e.getValue() + " " + e.getKey() + ";\n");
        }
        return sb.toString();
    }

    private String makeVarcond() {
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

    private String makeAssumption(boolean payable, boolean forConstructor) {
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
            if (!(("enum").equals(env.vars.get(var)) || ("Message").equals(env.vars.get(var)) || ("logical").equals(env.vars.get(var)) 
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

    private String makeHeapUpdate(String func, boolean payable, boolean forConstructor) {
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

    private String makeFunctionCall(String func, boolean forConstructor) {
        List<String> parameters = env.funcs.get(func).parameterOrder;
        String parString = "";
        for (String p : parameters) {
            parString = parString + ",_" + p;
        }
        if (forConstructor) {
            func = "<init>";
        }
        return "self." + func + "(msg" + parString + ")@" + contractName + ";";
    }

    private String makePostCondition(String func, boolean forConstructor) {
        String ret = "";
        // only_if:s
        if (posMap.get(func).onlyIf != null) {
            ret = " & " + posMap.get(func).onlyIf;
        }
        if (posMap.get(func).onSuccess != null) {
            ret = ret + " & " + posMap.get(func).onSuccess;
        }
        if (!forConstructor) { // assignable stuff
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
                elementOfString = injectHeap(SpecCompilerUtils.HeapType.OLD_HEAP, elementOfString);
            }
            ret = ret + "& (\\forall Field f; \\forall java.lang.Object o; (" + elementOfString + " !o = null & !o.<created>@savedHeap = TRUE | o.f = o.f@savedHeap))";
        }
        return ret; 
    }

    public static String injectHeap(SpecCompilerUtils.HeapType heap, String str) {
        return str.replaceAll(SoliditySpecVisitor.HEAP_PLACEHOLDER_STRING,heap.toString());
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
}
