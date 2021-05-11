import java.util.*;

import java.io.File;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URI;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

public class SoliditySpecPreVisitor extends SolidityBaseVisitor<String> {
    private Environment env = new Environment();
    private String contractName; 
    private int contractStartLine;

    public SoliditySpecPreVisitor(String contractName)  {
        env.vars.put("msg","Message");
        env.vars.put("all_addresses","logical");
        env.vars.put("balance","int");
        env.vars.put("this","");

        this.contractName = contractName;
    }

    public Environment getEnvironment() {
        return env;
    }

    public int getContractStartLine() {
        return contractStartLine;
    }

	@Override public String visitElementaryTypeName(SolidityParser.ElementaryTypeNameContext ctx) {
        return SpecCompilerUtils.solidityToJavaType(ctx.getText());
    }

	@Override public String visitUserDefinedTypeName(SolidityParser.UserDefinedTypeNameContext ctx) { 
        String type = ctx.identifier(0).Identifier().getText();
        String subtype = ctx.identifier(1) != null ?
            ctx.identifier(1).Identifier().getText() : null;
        if (subtype != null) {
            return type + "." + subtype;
        } else {
            return type;
        }
    }

	@Override public String visitTypeName(SolidityParser.TypeNameContext ctx) {
        if (ctx.typeName() != null) { // this is an array
            String typeName = visit(ctx.typeName());
            return typeName + "[]";
        } else {
            return visitChildren(ctx);
        }
    }

	@Override public String visitMapping(SolidityParser.MappingContext ctx) {
        String key = visit(ctx.elementaryTypeName());
        String value = visit(ctx.typeName());
        return value + "[]";
    }

    @Override public String visitStateVariableDeclaration(SolidityParser.StateVariableDeclarationContext ctx) { 
        String typeRes = visit(ctx.typeName());
//		env.vars.put(ctx.getText(), 
//			ctx.getRuleIndex());
        env.vars.put(ctx.identifier().Identifier().getText(), typeRes);
//        System.out.println(typeRes.type + " " + ctx.identifier().Identifier().getText());
		return null;
	}

	@Override public String visitEnumDefinition(SolidityParser.EnumDefinitionContext ctx) {
        String enumTypeName = ctx.identifier().Identifier().getText();
        env.enums.add(enumTypeName);
        return enumTypeName;
    }

	@Override public String visitContractDefinition(SolidityParser.ContractDefinitionContext ctx) {
        String currentContractName = ctx.identifier().Identifier().getText();
        if (contractName.equals(currentContractName)) {
            if (ctx.ContractKeyword() != null) {
                env.unitType = Environment.UnitType.CONTRACT;
            } else if (ctx.InterfaceKeyword() != null) {
                env.unitType = Environment.UnitType.INTERFACE;
            } else if (ctx.LibraryKeyword() != null) {
                env.unitType = Environment.UnitType.LIBRARY;
            }
            contractStartLine = ctx.start.getLine();
            return visitChildren(ctx);
        } else {
            return null;
        }
    }

	@Override public String visitFunctionDefinition(SolidityParser.FunctionDefinitionContext ctx) {
        String funcName = ctx.identifier().Identifier().getText();
        boolean payable = false;
        for (SolidityParser.StateMutabilityContext smc : ctx.modifierList().stateMutability()) {
            if (smc.PayableKeyword() != null) {
                payable = true;
                break;
            }
        }
        env.funcs.put(funcName, new Environment.FunctionInfo(payable, ctx.start.getLine()));
        List<SolidityParser.ParameterContext> pars = ctx.parameterList().parameter();
        for (SolidityParser.ParameterContext p : pars) {
            env.funcs.get(funcName).parameters.put(p.identifier().getText(),SpecCompilerUtils.solidityToJavaType(p.typeName().getText()));
            env.funcs.get(funcName).parameterOrder.add(p.identifier().getText());
        }
        if (ctx.returnParameters() != null) {
            env.funcs.get(funcName).returnType = SpecCompilerUtils.solidityToJavaType(
                ctx.returnParameters().parameterList().parameter(0).getText());
        }
        return "";
    }

	@Override public String visitConstructorDefinition(SolidityParser.ConstructorDefinitionContext ctx) {
        String funcName = contractName;
        boolean payable = false;
        for (SolidityParser.StateMutabilityContext smc : ctx.modifierList().stateMutability()) {
            if (smc.PayableKeyword() != null) {
                payable = true;
                break;
            }
        }
        env.funcs.put(funcName, new Environment.FunctionInfo(payable, ctx.start.getLine()));
        List<SolidityParser.ParameterContext> pars = ctx.parameterList().parameter();
        for (SolidityParser.ParameterContext p : pars) {
            env.funcs.get(funcName).parameters.put(p.identifier().Identifier().getText(),SpecCompilerUtils.solidityToJavaType(p.typeName().getText()));
            env.funcs.get(funcName).parameterOrder.add(p.identifier().Identifier().getText());
        }
        return "";
    }

    public void parse(String file) throws IOException {
		SolidityLexer lexer = new SolidityLexer(CharStreams.fromStream(new File(file).toURI().toURL().openStream()));
		SolidityParser parser = new SolidityParser(new CommonTokenStream(lexer));
		SolidityParser.SourceUnitContext solidityAST = parser.sourceUnit();
		visit(solidityAST);
    }
}
