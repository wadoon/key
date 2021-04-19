import java.util.*;

import java.io.File;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URI;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

public class SoliditySpecPreVisitor extends SolidityBaseVisitor<Result> {
	private Map<String,String> vars = new HashMap<>();
    public static Map<String,FunctionInfo> funcs = new HashMap<>();
    public static String contractName; // wow, ugly

    public static class FunctionInfo {
        public boolean payable;
        public int lineNo;
        public Map<String,String> parameters = new HashMap<>();
        public List<String> parameterOrder = new LinkedList<>();
        public FunctionInfo(boolean p,int l) {
            payable = p;
            lineNo = l;
        }
        public FunctionInfo() {};
        public String toString() {
            return "payable " + payable + " line no " + lineNo;
        }
    }
    public SoliditySpecPreVisitor() {
        vars.put("msg","Message");
        vars.put("all_addresses","logical");
        vars.put("balance","int");
        vars.put("this","");
    }

	@Override public Result visitElementaryTypeName(SolidityParser.ElementaryTypeNameContext ctx) {
        return new Result(solidityToJavaType(ctx.getText()), "");
    }

    public static String solidityToJavaType(String solType) {
        String ret;
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

	@Override public Result visitUserDefinedTypeName(SolidityParser.UserDefinedTypeNameContext ctx) { 
        String subtype = ctx.identifier(1) != null ?
            ctx.identifier(1).Identifier().getText() : null;
        return new Result(subtype == null ? ctx.identifier(0).Identifier().getText() : 
                ctx.identifier(0).Identifier().getText() + "." + subtype, "");
    
    }

	@Override public Result visitTypeName(SolidityParser.TypeNameContext ctx) {
        if (ctx.typeName() != null) { // this is an array
            Result typeName = visit(ctx.typeName());
            return new Result(typeName.type + "[]", "");
        } else {
            return visitChildren(ctx);
        }
    }

	@Override public Result visitMapping(SolidityParser.MappingContext ctx) {
        Result key = visit(ctx.elementaryTypeName());
        Result value = visit(ctx.typeName());
        return new Result(value.type + "[]", "");
    }

    @Override public Result visitStateVariableDeclaration(SolidityParser.StateVariableDeclarationContext ctx) { 
        Result typeRes = visit(ctx.typeName());
//		vars.put(ctx.getText(), 
//			ctx.getRuleIndex());
        vars.put(ctx.identifier().Identifier().getText(), typeRes.type);
//        System.out.println(typeRes.type + " " + ctx.identifier().Identifier().getText());
		return null;
	}

	@Override public Result visitEnumDefinition(SolidityParser.EnumDefinitionContext ctx) {
        vars.put(ctx.identifier().Identifier().getText(),"enum"); //uncertain if needed
        return new Result("enum", "");
    }

	@Override public Result visitContractDefinition(SolidityParser.ContractDefinitionContext ctx) {
        contractName = ctx.identifier().Identifier().getText() + "Impl";
        return visitChildren(ctx);
    }

	@Override public Result visitFunctionDefinition(SolidityParser.FunctionDefinitionContext ctx) {
        String funcName = ctx.identifier().Identifier().getText();
        boolean payable = false;
        for (SolidityParser.StateMutabilityContext smc : ctx.modifierList().stateMutability()) {
            if (smc.PayableKeyword() != null) {
                payable = true;
                break;
            }
        }
        funcs.put(funcName, new FunctionInfo(payable, ctx.start.getLine()));
        List<SolidityParser.ParameterContext> pars = ctx.parameterList().parameter();
        for (SolidityParser.ParameterContext p : pars) {
            funcs.get(funcName).parameters.put(p.identifier().getText(),solidityToJavaType(p.typeName().getText()));
            funcs.get(funcName).parameterOrder.add(p.identifier().getText());
        }
        return new Result("","");
    }

	@Override public Result visitConstructorDefinition(SolidityParser.ConstructorDefinitionContext ctx) {
        String funcName = contractName;
        boolean payable = false;
        for (SolidityParser.StateMutabilityContext smc : ctx.modifierList().stateMutability()) {
            if (smc.PayableKeyword() != null) {
                payable = true;
                break;
            }
        }
        funcs.put(funcName, new FunctionInfo(payable, ctx.start.getLine()));
        List<SolidityParser.ParameterContext> pars = ctx.parameterList().parameter();
        for (SolidityParser.ParameterContext p : pars) {
            funcs.get(funcName).parameters.put(p.identifier().Identifier().getText(),solidityToJavaType(p.typeName().getText()));
            funcs.get(funcName).parameterOrder.add(p.identifier().Identifier().getText());
        }
        return new Result("","");
    }

	public Map<String,String> getOutput() {
		return vars;
	}

    public static Map<String,String> parse(String file) throws IOException {
		SolidityLexer lexer = new SolidityLexer(CharStreams.fromStream(new File(file).toURI().toURL().openStream()));
		SolidityParser parser = new SolidityParser(new CommonTokenStream(lexer));
		SoliditySpecPreVisitor visitor = new SoliditySpecPreVisitor();
		SolidityParser.SourceUnitContext solidityAST = parser.sourceUnit();
		visitor.visit(solidityAST);
        return visitor.getOutput();
    }

	public static void main(String[] args) throws IOException {
		SolidityLexer lexer = new SolidityLexer(CharStreams.fromStream(new File(args[0]).toURI().toURL().openStream()));
		SolidityParser parser = new SolidityParser(new CommonTokenStream(lexer));
		SoliditySpecPreVisitor visitor = new SoliditySpecPreVisitor();
		SolidityParser.SourceUnitContext solidityAST = parser.sourceUnit();
		visitor.visit(solidityAST);
		System.out.println(visitor.getOutput());
	}
}
