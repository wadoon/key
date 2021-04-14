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

class Result {
    String type; String output;
    Result(String t, String o) {
        type = t; output = o;
    }
    public String toString() {
        return type + " " + output;
    }
}

public class SoliditySpecVisitor extends SolidityBaseVisitor<Result> {
    private static String CONTRACT_NAME_PLACEHOLDER = "__contract_name_placeholder__";
    private static String PROGRAM_VARIABLES_PLACEHOLDER = "__program_variables_placeholder__";
    private static String SCHEMA_VARIABLES_PLACEHOLDER = "__schema_variables_placeholder__";
    private static String INVARIANT_PLACEHOLDER = "__invariant_placeholder__";
    private static String ASSUMPTION_PLACEHOLDER = "__assumption_placeholder__";
    private static String FUNCTION_PLACEHOLDER = "__function_placeholder__";
    private static String POSTCONDITION_PLACEHOLDER = "__postcondition_placeholder__";
    private static String VARCOND_PLACEHOLDER = "__varcond_placeholder__";
    private static String HEAP_UPDATE_PLACEHOLDER = "__heap_update_placeholder__";

    private static String HEAP_PLACEHOLDER_STRING = "__heap__";

    private enum HeapType {HEAP, OLD_HEAP, HEAP_H};

    private static Map<HeapType,String> heapStrings = new HashMap<>();
    private static Map<String,String> vars;
    private static Map<String,String> cumulativeLogicalVars = new HashMap<>();
    
    private static String invariant;
    private static Map<String,String> onlyIfMap = new HashMap<>();
    private static Map<String,String> onSuccessMap = new HashMap<>();
    private static Map<String,List<String>> assignableMap = new HashMap<>();
    private static Map<String,Boolean> isGrossMap = new HashMap<>();

    private String contractName;
    private int startLineNo;

    static {
        heapStrings.put(HeapType.HEAP, "heap");
        heapStrings.put(HeapType.OLD_HEAP, "savedHeap");
        heapStrings.put(HeapType.HEAP_H, "h");
    }

    public SoliditySpecVisitor(String contractName, int startLineNo) {
        super();
        this.contractName = contractName;
        this.startLineNo = startLineNo;
        isGrossMap.put(functionFromLineNo(startLineNo),false);
    }

    @Override public Result visitSpecOnlyIf(SolidityParser.SpecOnlyIfContext ctx) {
        Result r = visitChildren(ctx);
        r.output = injectHeap(HeapType.OLD_HEAP, r.output);
        onlyIfMap.put(functionFromLineNo(startLineNo), r.output);
        return r;
    }

    @Override public Result visitSpecAssumes(SolidityParser.SpecAssumesContext ctx) { return visitChildren(ctx); }

	@Override public Result visitSpecAssignable(SolidityParser.SpecAssignableContext ctx) {
        List<SolidityParser.ExpressionContext> expressions = ctx.expression();
        String function = functionFromLineNo(startLineNo);
        assignableMap.put(function, new LinkedList<>());
        for (SolidityParser.ExpressionContext ec : expressions) {
            Result r = visit(ec);
            String beforeHeap = r.output.substring(0, r.output.indexOf(HEAP_PLACEHOLDER_STRING));
            // find number of opening parentheses in removed string
            int numParentheses = 0;
            for (int ind=0; ind!=-1 && ind<beforeHeap.length(); ) {
                ind = beforeHeap.indexOf('(', ind);
                if (ind != -1) {
                    numParentheses++;
                    ind++;
                }
            }
            r.output = r.output.substring(r.output.indexOf(HEAP_PLACEHOLDER_STRING)+HEAP_PLACEHOLDER_STRING.length()+1);
            r.output = r.output.substring(0,r.output.length()-numParentheses); // remove trailing parentheses 
            assignableMap.get(function).add(r.output);
        }
        return new Result("","");
    }

    @Override public Result visitSpecOnSuccess(SolidityParser.SpecOnSuccessContext ctx) { 
        Result r = visitChildren(ctx);
        r.output = injectHeap(HeapType.HEAP, r.output);
        onSuccessMap.put(functionFromLineNo(startLineNo), r.output);
        return r;
    }

    @Override public Result visitSpecClassInvariant(SolidityParser.SpecClassInvariantContext ctx) {
        Result r = visitChildren(ctx);
        invariant = injectHeap(HeapType.HEAP_H, r.output); // assuming only one invariant per contract
        r.output = invariant;
        return r;
    }

    @Override public Result visitArrayAccessExpression(SolidityParser.ArrayAccessExpressionContext ctx) {
        //dont forget implicit this/self
        Result r1 = visit(ctx.expression(0));
        Result r2 = visit(ctx.expression(1));
        String type = r1.type.substring(0,r1.type.length()-2);
        String intCast = !("int").equals(r2.type) ? "(int)" : "";
        String res = "(" + type + 
            "::select(" + HEAP_PLACEHOLDER_STRING + "," + r1.output + ", arr(" + intCast +  r2.output + ")))"; 
        return new Result(type,res);
    }

    @Override public Result visitNumberLiteral(SolidityParser.NumberLiteralContext ctx) {
        return new Result("int", ctx.DecimalNumber().getText());
    }
    
    @Override public Result visitIdentifier(SolidityParser.IdentifierContext ctx) { 
        String ident = ctx.Identifier().getText();
        String type = SoliditySpecPreVisitor.funcs.get(functionFromLineNo(startLineNo)).parameters.get(ident);
        if (type != null) {
            return new Result(type, ident);
        } else {
            type = vars.get(ident);
            if (("enum").equals(vars.get(type))) {
                type = contractName + "." + type;
            }
            String access = !type.equals("logical") ? 
                "(" + type + "::select(" + HEAP_PLACEHOLDER_STRING + ",self," +
                injectFieldPrefix(ident) + "))" :
                ident;
            return new Result(type, access);
        }
    }

    @Override public Result visitEqualityExpression(SolidityParser.EqualityExpressionContext ctx) {
        Result r1 = visit(ctx.expression(0));
        Result r2 = visit(ctx.expression(1));
        String op = ctx.binop.getText().equals("==") ? " = " : " != ";
        return new Result(r1.type, "(" + r1.output + op + r2.output + ")");
    }

    @Override public Result visitAndExpression(SolidityParser.AndExpressionContext ctx) {
        Result r1 = visit(ctx.expression(0));
        Result r2 = visit(ctx.expression(1));
        return new Result(r1.type, "(" + r1.output + " & " + r2.output + ")");
    }

    @Override public Result visitOrExpression(SolidityParser.OrExpressionContext ctx) {
        Result r1 = visit(ctx.expression(0));
        Result r2 = visit(ctx.expression(1));
        return new Result(r1.type, "(" + r1.output + " | " + r2.output + ")");
    }

    @Override public Result visitNotExpression(SolidityParser.NotExpressionContext ctx) {
        Result r = visit(ctx.expression());
        return new Result(r.type, "!(" + r.output + ")");
    }

    @Override public Result visitImplicationExpression(SolidityParser.ImplicationExpressionContext ctx) {
        Result r1 = visit(ctx.expression(0));
        Result r2 = visit(ctx.expression(1));
        return new Result(r1.type, "(" + r1.output + " -> " + r2.output + ")");
    }

    @Override public Result visitForallExpression(SolidityParser.ForallExpressionContext ctx) {
        cumulativeLogicalVars.put(ctx.Identifier().getText(), solidityToJavaType(ctx.typeName().getText()));
        vars.put(ctx.Identifier().getText(), "logical");
        Result r = visit(ctx.expression());
        Result ret = new Result(r.type, "(\\forall " + 
            ctx.Identifier().getText() + "; " + 
            r.output + ")");
        vars.remove(ctx.Identifier().getText());
        return ret;
    }

    private String solidityToJavaType(String solType) {
        String ret = null;
        switch (solType) {
            case "uint":
            case "uint256":
                ret = "int";
                break;
            case "bool":
                ret = "boolean";
                break;
            case "address":
                ret = "Address";
                break;
            default:
                ret = solType;
                break;
        }
        return ret;
    }

    @Override public Result visitExistsExpression(SolidityParser.ExistsExpressionContext ctx) {
        cumulativeLogicalVars.put(ctx.Identifier().getText(), solidityToJavaType(ctx.typeName().getText()));
        vars.put(ctx.Identifier().getText(), "logical");
        Result r = visit(ctx.expression());
        Result ret = new Result(r.type, "(\\exists " + 
            ctx.Identifier().getText() + "; " + 
            r.output + ")");
        vars.remove(ctx.Identifier().getText());
        return ret;
    }

    @Override public Result visitCompExpression(SolidityParser.CompExpressionContext ctx) {
        Result r1 = visit(ctx.expression(0));
        Result r2 = visit(ctx.expression(1));
        String op = ctx.binop.getText();
        return new Result(r1.type, "(" + r1.output + " " + op + " " + r2.output + ")");
    }

	@Override public Result visitNetExpression(SolidityParser.NetExpressionContext ctx) { 
        Result r = visit(ctx.expression());
        return returnFromNetGross(r, "net");
    }

	@Override public Result visitGrossToExpression(SolidityParser.GrossToExpressionContext ctx) { 
        isGrossMap.put(functionFromLineNo(startLineNo),true);
        Result r = visit(ctx.expression());
        return returnFromNetGross(r, "gross_to");
    }

	@Override public Result visitGrossFromExpression(SolidityParser.GrossFromExpressionContext ctx) { 
        isGrossMap.put(functionFromLineNo(startLineNo),true);
        Result r = visit(ctx.expression());
        return returnFromNetGross(r, "gross_from");
    }
   
    public Result returnFromNetGross(Result r, String func) {
        Result ret = new Result("int",null);
        ret.output = "int::select(" + HEAP_PLACEHOLDER_STRING + "," + func + ",address(" + r.output + "))";
        return ret;
    }
	@Override public Result visitEquivalenceExpression(SolidityParser.EquivalenceExpressionContext ctx) {
        Result r1 = visit(ctx.expression(0));
        Result r2 = visit(ctx.expression(1));
        return new Result(r1.type,"((" + r1.output + ")<->(" + r2.output + "))");
    }

	@Override public Result visitDotExpression(SolidityParser.DotExpressionContext ctx) {
        Result r = visit(ctx.expression());
        String ident = ctx.identifier().Identifier().getText();
//        System.out.println(ident);
//        System.out.println(r.type);
//        System.out.println(r.output);
        String typeOutput = contractName + "." + ctx.expression().getText();
        String type = null;
        String output = null;
        if (r.type.equals("enum")) {
            type = r.type;
            output = typeOutput + "::select(" + HEAP_PLACEHOLDER_STRING + ",null," + typeOutput + "::$" + ident + ")";
        } else if (ident.equals("length") || ident.equals("arr_length")) {
            type = "int";
            output = "(" + "int" + "::select(" + HEAP_PLACEHOLDER_STRING + "," + r.output + "," + ident + "))";
            
        } else if (r.type.equals("Message")) {    // assuming either msg.sender or msg.value
            type = ident.equals("sender") ? "Address" : "int";
            output = "(" + type + "::select(" + HEAP_PLACEHOLDER_STRING + ",msg,java.lang.Message::$" + ident + "))";
        } else {
            throw new RuntimeException("unsupported expression in dot expression");
        }
        return new Result(type, output);
    }

	@Override public Result visitPrimaryExpression(SolidityParser.PrimaryExpressionContext ctx) {
        if (ctx.BooleanLiteral() != null) {
            return new Result("boolean", ctx.BooleanLiteral().getText().toUpperCase());
        } else {
            return visitChildren(ctx);
        }
    }

	@Override public Result visitAdditiveExpression(SolidityParser.AdditiveExpressionContext ctx) {
        Result r1 = visit(ctx.expression(0));
        Result r2 = visit(ctx.expression(1));
        return new Result(r1.type, "(" + r1.output + ctx.binop.getText() + r2.output + ")");
    }

	@Override public Result visitMultiplicativeExpression(SolidityParser.MultiplicativeExpressionContext ctx) {
        Result r1 = visit(ctx.expression(0));
        Result r2 = visit(ctx.expression(1));
        return new Result(r1.type, "(" + r1.output + ctx.binop.getText() + r2.output + ")");
    }

	@Override public Result visitOldExpression(SolidityParser.OldExpressionContext ctx) {
        Result r = visitChildren(ctx);
        r.output = injectHeap(HeapType.OLD_HEAP, r.output);
        return r;
    }

    @Override public Result aggregateResult(Result agg, Result next) {
        if (agg == null) {
            return next;
        } else if (next == null) {
            return agg;
        } else {
            return next; //TODO arbitrary, come up with better idea
        }
    }

    public static String injectHeap(HeapType heap, String str) {
        return str.replaceAll(HEAP_PLACEHOLDER_STRING,heapString(heap));
    }

    public String injectFieldPrefix(String str) {
        return contractName + "::$" + str;
    }

    public static String heapString(HeapType h) {
        return heapStrings.get(h);
    }

    private static String functionFromLineNo(int line) {
        String currentFunction = null;
        int currentFunctionLineNo = line;
        for (Map.Entry<String,SoliditySpecPreVisitor.FunctionInfo> e : SoliditySpecPreVisitor.funcs.entrySet()) {
            if (e.getValue().lineNo > line && 
                        (currentFunctionLineNo == line || e.getValue().lineNo < currentFunctionLineNo)) {
                currentFunction = e.getKey();
                currentFunctionLineNo = e.getValue().lineNo;
            }
        }
        return currentFunction;
    }
    
    public static void main(String[] args) throws IOException {
        // first pass
        vars = SoliditySpecPreVisitor.parse(args[0]);
//System.out.println(vars);
        // second pass
        CharStream c = CharStreams.fromStream(new File(args[0]).toURI().toURL().openStream());
        SolidityLexer lexer = new SolidityLexer(c);
            Token t = null;
            while ((t = lexer.nextToken()).getType() != Token.EOF) {
                if (t.getChannel() == 2 || t.getChannel() == 3) {
                    // create parser, parse t
                    // join with some larger proof obl structure
                    String toParse = t.getChannel() == 2 ? t.getText().substring(3,t.getText().length()-2) : t.getText().substring(3);
//                    System.out.println("to parse: " + toParse);
                    CharStream c2 = CharStreams.fromString(toParse,"dummy");
                    SolidityLexer lexer2 = new SolidityLexer(c2);
                    CommonTokenStream cts2 = new CommonTokenStream(lexer2);
                    SolidityParser parser2 = new SolidityParser(cts2);
                    SolidityParser.SpecDefinitionContext solidityAST = parser2.specDefinition();
                    SoliditySpecVisitor visitor2 = new SoliditySpecVisitor(SoliditySpecPreVisitor.contractName, t.getLine());
                    Result r = visitor2.visit(solidityAST);
                }
            }
        String funcName = args[1];
        if (!SoliditySpecPreVisitor.funcs.containsKey(funcName)) {
            System.out.println("Could not find function " + funcName);
            System.exit(-1);
        }
        boolean funcPayable = SoliditySpecPreVisitor.funcs.get(funcName).payable;
        boolean forConstructor = funcName.equals(SoliditySpecPreVisitor.contractName);
        String output = loadTemplate();
        output = output.replace(INVARIANT_PLACEHOLDER, invariant != null ? invariant : "true")
                       .replace(CONTRACT_NAME_PLACEHOLDER, SoliditySpecPreVisitor.contractName)
                       .replace(PROGRAM_VARIABLES_PLACEHOLDER, makeProgramVariables(funcName))
                       .replace(SCHEMA_VARIABLES_PLACEHOLDER, makeSchemaVariables())
                       .replace(VARCOND_PLACEHOLDER, makeVarcond())
                       .replace(ASSUMPTION_PLACEHOLDER, makeAssumption(funcPayable,forConstructor))
                       .replace(HEAP_UPDATE_PLACEHOLDER, makeHeapUpdate(funcName, funcPayable, forConstructor))
                       .replace(FUNCTION_PLACEHOLDER, makeFunctionCall(funcName,forConstructor))
                       .replace(POSTCONDITION_PLACEHOLDER, makePostCondition(funcName,forConstructor));
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

    private static String makeProgramVariables(String func) {
        Map<String,String> parameters = SoliditySpecPreVisitor.funcs.get(func).parameters;
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

    private static String makeSchemaVariables() {
        StringBuilder sb = new StringBuilder();
        for(Map.Entry<String,String> e : cumulativeLogicalVars.entrySet()) {
            sb.append("\\schemaVar \\variable " + e.getValue() + " " + e.getKey() + ";\n");
        }
        return sb.toString();
    }

    private static String makeVarcond() {
        StringBuilder sb = new StringBuilder();
        for (Map.Entry<String,String> e : cumulativeLogicalVars.entrySet()) {
            sb.append("\\notFreeIn(" + e.getKey() + "," + heapStrings.get(HeapType.HEAP_H) + ",self),");
        }
        if (sb.length() > 0) {
            sb.deleteCharAt(sb.length()-1);
        } else {
           return "";
        }
        return "\\varcond(" + sb.toString() + ")";
    }

    private static String makeAssumption(boolean payable, boolean forConstructor) {
        StringBuilder sb = new StringBuilder();
        if (!forConstructor) {
            sb.append("&\nCInv(heap,self) ");
        }
        if (payable) {
            sb.append("&\nmsg.value >= 0 ");
        } else {
            sb.append("&\nmsg.value = 0 ");
        }
        for (String var : vars.keySet()) {
            if (!(("enum").equals(vars.get(var)) || ("Message").equals(vars.get(var)))) {
                sb.append("&\nself." + var + "!= null " );
            }
        }
        if (forConstructor) {
            sb.append("&\n(\\forall Address a; int::select(heap,net,address(a))=0) ");
            // assumptions for state variable values
            for (Map.Entry<String,String> p : vars.entrySet()) {
                if (!(("enum").equals(p.getValue()) || ("Message").equals(vars.get(p.getValue())))) {
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

    private static String makeHeapUpdate(String func, boolean payable, boolean forConstructor) {
        String parString = "";
        for (String p : SoliditySpecPreVisitor.funcs.get(func).parameterOrder) {
            parString = parString + " || _" + p + " := " + p;
        }

        String mapping = isGrossMap.get(func) ? "gross_from" : "net";
        return payable ?
            ( forConstructor ? 
            parString + "|| heap:=store(heap," + mapping + ", address(msg.sender),msg.value)" :
            parString + "|| heap:=store(heap, " + mapping + ", address(msg.sender), int::select(heap, " + mapping + ", address(msg.sender)) + msg.value)"
            ) :
            parString;
    }

    private static String makeFunctionCall(String func, boolean forConstructor) {
        List<String> parameters = SoliditySpecPreVisitor.funcs.get(func).parameterOrder;
        String parString = "";
        for (String p : parameters) {
            parString = parString + ",_" + p;
        }
        if (forConstructor) {
            func = "<init>";
        }
        return "self." + func + "(msg" + parString + ")@" + SoliditySpecPreVisitor.contractName + ";";
    }

    private static String makePostCondition(String func, boolean forConstructor) {
        String ret = "";
        // only_if:s
        if (onlyIfMap.get(func) != null) {
            ret = " & " + onlyIfMap.get(func);
        }
        if (onSuccessMap.get(func) != null) {
            ret = ret + " & " + onSuccessMap.get(func);
        }
        if (!forConstructor) {
            String elementOfString = "";
            List<String> objFields = assignableMap.get(func);
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
                elementOfString = injectHeap(HeapType.OLD_HEAP, elementOfString);
            }
            ret = ret + "& (\\forall Field f; \\forall java.lang.Object o; (" + elementOfString + " !o = null & !o.<created>@savedHeap = TRUE | o.f = o.f@savedHeap))";
        }
        return ret; 
    }
}
