package de.uka.ilkd.key.parser.solidity;

import java.util.*;
import java.util.regex.Matcher;

public class SoliditySpecVisitor extends SolidityBaseVisitor<SoliditySpecVisitor.SMLExpr> {
    static class SMLExpr {
        String type; // Solidity type
        String output;
        SMLExpr(String type, String output) {
            this.type = type; this.output = output;
        }
        public String toString() {
            return type + " " + output;
        }
    }

    private static final String __VARIABLE_PLACEHOLDER__ = "__variable_placeholder__";
    private static final String __QUANT_TYPE_START__ = "__quant_type_start__";
    private static final String __QUANT_TYPE_END__ = "__quant_type_end__";

    private final ProofObligations pos;
    private final Environment env;
    private final String contractNameInPOs;
    private final Solidity.Callable callable;
    private final Solidity.Contract contract;
    private final boolean onlyLibraryInvariant;
    private String placeHolderType; // for use with library invariants which are really "template" invariants

    public SoliditySpecVisitor(String contractNameInPOs, Solidity.Callable callable, Solidity.Contract contract,
                               Environment env, ProofObligations pos, boolean onlyLibraryInvariant) {
        super();
        this.contractNameInPOs = contractNameInPOs;
        this.callable = callable;
        this.contract = contract;
        this.env = env;
        this.pos  = pos;
        this.onlyLibraryInvariant = onlyLibraryInvariant;
    }

    private void error(String string) throws RuntimeException {
        throw new RuntimeException(string);
    }

    @Override public SMLExpr visitSpecOnlyIf(SolidityParser.SpecOnlyIfContext ctx) {
        if (onlyLibraryInvariant) {
            return null;
        }
        SMLExpr r = visitChildren(ctx);
        r.output = SpecCompilerUtils.injectHeap(SpecCompilerUtils.HeapType.OLD_HEAP, r.output);
        r.output = resolveQuantifiesForNonTaclet(r.output);
        pos.addOnlyIf(callable.name, r.output);
        return r;
    }

    @Override public SMLExpr visitSpecAssumes(SolidityParser.SpecAssumesContext ctx) { 
        if (onlyLibraryInvariant) {
            return null;
        }
        SMLExpr r = visitChildren(ctx);
        r.output = SpecCompilerUtils.injectHeap(SpecCompilerUtils.HeapType.HEAP, r.output);
        r.output = resolveQuantifiesForNonTaclet(r.output);
        pos.addAssumes(callable.name, r.output);
        return r;
    }

	@Override public SMLExpr visitSpecAssignable(SolidityParser.SpecAssignableContext ctx) {
        if (onlyLibraryInvariant) {
            return null;
        }
        List<SolidityParser.ExpressionContext> expressions = ctx.expression();
        for (SolidityParser.ExpressionContext ec : expressions) {
            SMLExpr r = visit(ec);
            String beforeHeap = r.output.substring(0, r.output.indexOf(SpecCompilerUtils.HEAP_PLACEHOLDER_STRING));
            // find number of opening parentheses in removed string
            int numParentheses = 0;
            for (int ind=0; ind!=-1 && ind<beforeHeap.length(); ) {
                ind = beforeHeap.indexOf('(', ind);
                if (ind != -1) {
                    numParentheses++;
                    ind++;
                }
            }
            r.output = r.output.substring(r.output.indexOf(SpecCompilerUtils.
                HEAP_PLACEHOLDER_STRING)+SpecCompilerUtils.HEAP_PLACEHOLDER_STRING.length()+1);
            r.output = r.output.substring(0,r.output.length()-numParentheses); // remove trailing parentheses 
            r.output = resolveQuantifiesForNonTaclet(r.output);
            pos.addAssignable(callable.name, r.output);
        }
        return new SMLExpr("","");
    }

    @Override public SMLExpr visitSpecOnSuccess(SolidityParser.SpecOnSuccessContext ctx) { 
        if (onlyLibraryInvariant) {
            return null;
        }
        SMLExpr r = visitChildren(ctx);
        r.output = SpecCompilerUtils.injectHeap(SpecCompilerUtils.HeapType.HEAP, r.output);
        r.output = resolveQuantifiesForNonTaclet(r.output);
        pos.addOnSuccess(callable.name, r.output);
        return r;
    }

    @Override public SMLExpr visitSpecContractInvariant(SolidityParser.SpecContractInvariantContext ctx) {
        if (onlyLibraryInvariant) {
            return null;
        }
        SMLExpr r = visitChildren(ctx);
        r.output = SpecCompilerUtils.injectHeap(SpecCompilerUtils.HeapType.HEAP_H, r.output); // assuming only one invariant per contract
        r.output = resolveQuantifiesForTaclet(r.output);
        pos.addInvariant(r.output);
        return r;
    }

	@Override public SMLExpr visitSpecLibraryInvariant(SolidityParser.SpecLibraryInvariantContext ctx) {
        String type = ctx.typeName().getText();
        String ident = ctx.Identifier().getText();
        contract.fields.add(new Solidity.Field(ident, __VARIABLE_PLACEHOLDER__));
        placeHolderType = type;
        SMLExpr s = visit(ctx.expressionStatement());
        pos.setLibraryInvariant(s.output);
        contract.removeFieldWithIdent(ident);
        return s; 
    }

	@Override public SMLExpr visitSpecObservesInvariantFor(SolidityParser.SpecObservesInvariantForContext ctx) {
        if (onlyLibraryInvariant) {
            return null;
        }
        // We assume that there is only one lib invariant,
        // no need to parse second identifier
        SMLExpr ident = visit(ctx.identifier(0));
        String appliedInvariant = pos.libInvariantTemplate.replaceAll(__VARIABLE_PLACEHOLDER__,
            Matcher.quoteReplacement(ident.output));
        // Check if ident is parameter (otherwise it is a state variable)
        boolean identIsParam = false;
        for (Solidity.Variable param : callable.params) {
            if (param.name.equals(ctx.identifier(0).getText())) {
                identIsParam = true;
                break;
            }
        }
        if (identIsParam) {
            // ctx.identifier(0) is a parameter
            appliedInvariant = SpecCompilerUtils.injectHeap(SpecCompilerUtils.HeapType.HEAP, appliedInvariant);
            appliedInvariant = resolveQuantifiesForNonTaclet(appliedInvariant);
            pos.addAssumes(callable.name, appliedInvariant);
            pos.addOnSuccess(callable.name, appliedInvariant);
        } else {
            // ctx.identifier(0) is a state variable
            appliedInvariant = SpecCompilerUtils.injectHeap(SpecCompilerUtils.HeapType.HEAP_H, appliedInvariant);
            appliedInvariant = resolveQuantifiesForTaclet(appliedInvariant);
            pos.addInvariant(appliedInvariant);
        }
        return new SMLExpr("spec", null);
    }

    @Override public SMLExpr visitArrayAccessExpression(SolidityParser.ArrayAccessExpressionContext ctx) {
        //dont forget implicit this/self
        SMLExpr r1 = visit(ctx.expression(0));
        SMLExpr r2 = visit(ctx.expression(1));
        String underlyingArrayType = Solidity.solidityToJavaType(r1.type);
        underlyingArrayType = underlyingArrayType.substring(0, underlyingArrayType.length() - 2);
        String intCast = !("int").equals(r2.type) ? "(int)" : "";
        String res = "(" + Solidity.solidityToJavaType(underlyingArrayType) +
            "::select(" + SpecCompilerUtils.HEAP_PLACEHOLDER_STRING + "," + r1.output + ", arr(" + intCast +  r2.output + ")))"; 
        return new SMLExpr(underlyingArrayType,res);
    }

    @Override public SMLExpr visitNumberLiteral(SolidityParser.NumberLiteralContext ctx) {
        return new SMLExpr("int", ctx.DecimalNumber().getText());
    }
    
    @Override public SMLExpr visitIdentifier(SolidityParser.IdentifierContext ctx) { 
        String ident = ctx.Identifier() != null ? ctx.Identifier().getText() : ctx.getText();
        if (ident.equals("this")) {
            return new SMLExpr(contract.name, "self");
        }
        if (ident.equals("msg")) {
            return new SMLExpr("Message", "msg");
        }
        boolean identIsParam = false;
        String paramType = null;
        for (Solidity.Variable param : callable.params) {
            if (ident.equals(param.name)) {
                identIsParam = true;
                paramType = param.typename;
                break;
            }
        }
        if (identIsParam) {
            return new SMLExpr(paramType, ident);
        }
        String type = null;
        Solidity.Enum enum_ = null;
        Solidity.Struct struct = null;
        Solidity.Variable variable = null;
        if ((enum_ = contract.lookupEnum(ident, env.contracts)) != null) {
            type = enum_.toString();
        } else if ((struct = contract.lookupStruct(ident, env.contracts)) != null) {
            type = struct.toString();
        } else if ((variable = contract.lookupField(ident)) != null) {
            if ((enum_ = contract.lookupEnum(variable.typename, env.contracts)) != null) {
                type = enum_.toString();
            } else if ((struct = contract.lookupStruct(variable.typename, env.contracts)) != null) {
                type = struct.toString();
            } else {
                type = variable.typename;
            }
        } else if ((variable = env.cumulativeLogicalVars.get(ident)) != null) {
            type = variable.typename;
        } else {
            error("Could not find type of identifier " + ident);
        }
        if (type == null) {
            error("Could not find type of identifier " + ident);
        }
        if (type.equals(__VARIABLE_PLACEHOLDER__)) {
            return new SMLExpr(placeHolderType, __VARIABLE_PLACEHOLDER__);
        }
        boolean logicalVar = variable != null && variable instanceof Solidity.LogicalVariable;
        String access = logicalVar ? ident :
                "(" + Solidity.solidityToJavaType(type) + "::select(" +
                        SpecCompilerUtils.HEAP_PLACEHOLDER_STRING + ",self," + injectFieldPrefix(ident) + "))";
        return new SMLExpr(type, access);

    }

    @Override public SMLExpr visitEqualityExpression(SolidityParser.EqualityExpressionContext ctx) {
        SMLExpr r1 = visit(ctx.expression(0));
        SMLExpr r2 = visit(ctx.expression(1));
        String op = ctx.binop.getText().equals("==") ? " = " : " != ";
        return new SMLExpr("bool", "(" + r1.output + op + r2.output + ")");
    }

    @Override public SMLExpr visitAndExpression(SolidityParser.AndExpressionContext ctx) {
        SMLExpr r1 = visit(ctx.expression(0));
        SMLExpr r2 = visit(ctx.expression(1));
        return new SMLExpr("bool", "(" + r1.output + " & " + r2.output + ")");
    }

    @Override public SMLExpr visitOrExpression(SolidityParser.OrExpressionContext ctx) {
        SMLExpr r1 = visit(ctx.expression(0));
        SMLExpr r2 = visit(ctx.expression(1));
        return new SMLExpr("bool", "(" + r1.output + " | " + r2.output + ")");
    }

    @Override public SMLExpr visitNotExpression(SolidityParser.NotExpressionContext ctx) {
        SMLExpr r = visit(ctx.expression());
        return new SMLExpr("bool", "!(" + r.output + ")");
    }

    @Override public SMLExpr visitImplicationExpression(SolidityParser.ImplicationExpressionContext ctx) {
        SMLExpr r1 = visit(ctx.expression(0));
        SMLExpr r2 = visit(ctx.expression(1));
        return new SMLExpr("bool", "(" + r1.output + " -> " + r2.output + ")");
    }

    @Override public SMLExpr visitForallExpression(SolidityParser.ForallExpressionContext ctx) {
        String logicalVarName = ctx.Identifier().getText();
        String logicalVarType = ctx.typeName().getText();
        env.addLogicalVar(logicalVarName, logicalVarType);
        SMLExpr r = visit(ctx.expression());
        SMLExpr ret = new SMLExpr(r.type, "(\\forall " +
                __QUANT_TYPE_START__ + Solidity.solidityToJavaType(logicalVarType) + " " + __QUANT_TYPE_END__ +
                logicalVarName + "; " +
                r.output + ")");
        env.removeLogicalVar(logicalVarName);
        return ret;
    }

    @Override public SMLExpr visitExistsExpression(SolidityParser.ExistsExpressionContext ctx) {
        String logicalVarName = ctx.Identifier().getText();
        String logicalVarType = ctx.typeName().getText();
        env.addLogicalVar(logicalVarName, logicalVarType);
        SMLExpr r = visit(ctx.expression());
        SMLExpr ret = new SMLExpr(r.type, "(\\exists " +
            __QUANT_TYPE_START__ + Solidity.solidityToJavaType(logicalVarType) + " " + __QUANT_TYPE_END__ +
                logicalVarName + "; " +
            r.output + ")");
        env.removeLogicalVar(logicalVarName);
        return ret;
    }

    @Override public SMLExpr visitCompExpression(SolidityParser.CompExpressionContext ctx) {
        SMLExpr r1 = visit(ctx.expression(0));
        SMLExpr r2 = visit(ctx.expression(1));
        String op = ctx.binop.getText();
        return new SMLExpr("bool", "(" + r1.output + " " + op + " " + r2.output + ")");
    }

	@Override public SMLExpr visitNetExpression(SolidityParser.NetExpressionContext ctx) { 
        SMLExpr r = visit(ctx.expression());
        return returnFromNetGross(r, "net");
    }

	@Override public SMLExpr visitGrossToExpression(SolidityParser.GrossToExpressionContext ctx) { 
        pos.setGross(callable.name, true);
        SMLExpr r = visit(ctx.expression());
        return returnFromNetGross(r, "gross_to");
    }

	@Override public SMLExpr visitGrossFromExpression(SolidityParser.GrossFromExpressionContext ctx) { 
        pos.setGross(callable.name, true);
        SMLExpr r = visit(ctx.expression());
        return returnFromNetGross(r, "gross_from");
    }
   
    public SMLExpr returnFromNetGross(SMLExpr r, String func) {
        SMLExpr ret = new SMLExpr("int",null);
        ret.output = "int::select(" + SpecCompilerUtils.HEAP_PLACEHOLDER_STRING + "," + func + "," + (!r.output.equals("all_addresses") ? "address" : "") + "(" + r.output + "))";
        return ret;
    }
	@Override public SMLExpr visitEquivalenceExpression(SolidityParser.EquivalenceExpressionContext ctx) {
        SMLExpr r1 = visit(ctx.expression(0));
        SMLExpr r2 = visit(ctx.expression(1));
        return new SMLExpr("bool","((" + r1.output + ")<->(" + r2.output + "))");
    }

	@Override public SMLExpr visitDotExpression(SolidityParser.DotExpressionContext ctx) {
        // TODO: this does not consider all possible dot expression that can exist
        SMLExpr r = visit(ctx.expression());
        String ident = ctx.identifier().Identifier().getText();
        String type = null;
        String output = null;
        Solidity.Enum enum_ = contract.lookupEnum(r.type, env.contracts);
        if (enum_ != null) {
            type = enum_.toString();
            output = enum_ + "::select(" + SpecCompilerUtils.HEAP_PLACEHOLDER_STRING +
                    ",null," + enum_ + "::$" + ident + ")";
        } else if (ident.equals("length") || ident.equals("arr_length")) {
            ident = "arr_length";
            type = "int";
            output = "(" + "int" + "::select(" + SpecCompilerUtils.HEAP_PLACEHOLDER_STRING + "," + r.output + "," + ident + "))";
        } else if (r.type.equals("Message")) {    // assuming either msg.sender or msg.value
            type = ident.equals("sender") ? "Address" : "int";
            output = "(" + Solidity.solidityToJavaType(type) + "::select(" + SpecCompilerUtils.HEAP_PLACEHOLDER_STRING +
                    ",msg,java.lang.Message::$" + ident + "))";
        } else if (r.output.equals("this") && ident.equals("balance")) {
            type = contract.lookupField(ident).typename;
            output = "(" + Solidity.solidityToJavaType(type) + "::select(" + SpecCompilerUtils.HEAP_PLACEHOLDER_STRING +
                    ",self,java.lang.Address::$" + ident + "))";
        } else {
            Solidity.Struct struct = contract.lookupStruct(r.type, env.contracts);
            if (struct == null) {
                struct = contract.lookupStruct(ident, env.contracts);
                if (struct == null) {
                    error("unsupported expression in dot expression");
                }
            }
            Solidity.Variable structMember = struct.getVariableWithName(ident);
            if (structMember == null) {
                error("unsupported expression in dot expression");
            }
            type = structMember.typename;
            output = "(" + Solidity.solidityToJavaType(type) + "::select(" + SpecCompilerUtils.HEAP_PLACEHOLDER_STRING +
                    "," + r.output + ","  + Solidity.solidityToJavaType(r.type) + "::$" + ident + "))";
        }

        return new SMLExpr(type, output);
    }

	@Override public SMLExpr visitPrimaryExpression(SolidityParser.PrimaryExpressionContext ctx) {
        if (ctx.BooleanLiteral() != null) {
            return new SMLExpr("boolean", ctx.BooleanLiteral().getText().toUpperCase());
        } else {
            return visitChildren(ctx);
        }
    }

	@Override public SMLExpr visitAdditiveExpression(SolidityParser.AdditiveExpressionContext ctx) {
        SMLExpr r1 = visit(ctx.expression(0));
        SMLExpr r2 = visit(ctx.expression(1));
        return new SMLExpr(r1.type, "(" + r1.output + ctx.binop.getText() + r2.output + ")");
    }

	@Override public SMLExpr visitMultiplicativeExpression(SolidityParser.MultiplicativeExpressionContext ctx) {
        SMLExpr r1 = visit(ctx.expression(0));
        SMLExpr r2 = visit(ctx.expression(1));
        return new SMLExpr(r1.type, "(" + r1.output + ctx.binop.getText() + r2.output + ")");
    }

	@Override public SMLExpr visitOldExpression(SolidityParser.OldExpressionContext ctx) {
        SMLExpr r = visitChildren(ctx);
        r.output = SpecCompilerUtils.injectHeap(SpecCompilerUtils.HeapType.OLD_HEAP, r.output);
        return r;
    }

	@Override public SMLExpr visitResultExpression(SolidityParser.ResultExpressionContext ctx) {
        String type;
        if (callable instanceof Solidity.Function) {
            type = callable.returnType;
        } else {
            type = "void";
        }
        if (type.equals("void")) {
            error("Referring to result of a void function");
        }
        return new SMLExpr(type, "_result");
    }

    // this was implemented somewhat arbitrarily, don't know if it should be changed
    @Override public SMLExpr aggregateResult(SMLExpr agg, SMLExpr next) {
        if (agg == null) {
            return next;
        } else return Objects.requireNonNullElse(next, agg);
    }

    public String injectFieldPrefix(String str) {
        if (str.equals("balance")) 
            return "java.lang.Address::$balance";
        return contractNameInPOs + "::$" + str;
    }

    private String resolveQuantifiesForTaclet(String str) {
        return str.replaceAll(__QUANT_TYPE_START__ + ".*?" + __QUANT_TYPE_END__, "");
    }

    private String resolveQuantifiesForNonTaclet(String str) {
        return str.replaceAll(__QUANT_TYPE_START__,"").replaceAll(__QUANT_TYPE_END__,"");
    }
}
