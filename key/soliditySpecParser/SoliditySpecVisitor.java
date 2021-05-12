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

public class SoliditySpecVisitor extends SolidityBaseVisitor<SoliditySpecVisitor.SMLExpr> {

    static class SMLExpr {
        String type; String output;
        SMLExpr(String t, String o) {
            type = t; output = o;
        }
        public String toString() {
            return type + " " + output;
        }
    }

    enum SMLStatementType {
        CONTRACT_INVARIANT,
        LIBRARY_INVARIANT,
        ASSUMES,
        ON_SUCCESS,
        ONLY_IF,
        ASSIGNABLE
    }

    private final String __VARIABLE_PLACEHOLDER__ = "__variable_placeholder__";

    public ProofObligations pos;
    private Environment env;
    public String libInvariant;
    private String contractNameInPOs;
    private String function;
    private SMLStatementType stmtType;
    private Map<String,String> enumToKeYType = new HashMap<>();
    private String placeHolderType; // for use with library invariants which are really "template" invariants

    public SoliditySpecVisitor(String contractNameInPOs, String function, Environment env, ProofObligations pos) {
        super();
        this.contractNameInPOs = contractNameInPOs;
        this.function = function;
        this.env = env;
        this.pos  = pos;
    }

    @Override public SMLExpr visitSpecOnlyIf(SolidityParser.SpecOnlyIfContext ctx) {
        stmtType = SMLStatementType.ONLY_IF;
        SMLExpr r = visitChildren(ctx);
        r.output = SpecCompilerUtils.injectHeap(SpecCompilerUtils.HeapType.OLD_HEAP, r.output);
        pos.addOnlyIf(function, r.output);
        return r;
    }

    @Override public SMLExpr visitSpecAssumes(SolidityParser.SpecAssumesContext ctx) { 
        stmtType = SMLStatementType.ASSUMES;
        SMLExpr r = visitChildren(ctx);
        r.output = SpecCompilerUtils.injectHeap(SpecCompilerUtils.HeapType.HEAP, r.output);
        pos.addAssumes(function, r.output);
        return r;
    }

	@Override public SMLExpr visitSpecAssignable(SolidityParser.SpecAssignableContext ctx) {
        stmtType = SMLStatementType.ASSIGNABLE;
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
            pos.addAssignable(function, r.output);
        }
        return new SMLExpr("","");
    }

    @Override public SMLExpr visitSpecOnSuccess(SolidityParser.SpecOnSuccessContext ctx) { 
        stmtType = SMLStatementType.ON_SUCCESS;
        SMLExpr r = visitChildren(ctx);
        r.output = SpecCompilerUtils.injectHeap(SpecCompilerUtils.HeapType.HEAP, r.output);
        pos.addOnSuccess(function, r.output);
        return r;
    }

    @Override public SMLExpr visitSpecClassInvariant(SolidityParser.SpecClassInvariantContext ctx) {
        stmtType = SMLStatementType.CONTRACT_INVARIANT;
        SMLExpr r = visitChildren(ctx);
        String invariant = SpecCompilerUtils.injectHeap(SpecCompilerUtils.HeapType.HEAP_H, r.output); // assuming only one invariant per contract
        r.output = invariant;
        pos.addInvariant(invariant);
        return r;
    }

/*	@Override public SMLExpr visitSpecLibraryInvariant(SolidityParser.SpecLibraryInvariantContext ctx) {
        stmtType = SMLStatementType.LIBRARY_INVARIANT;
        String type = ctx.typeName().getText();
        String ident = ctx.Identifier().getText(); 
        env.addVariable(ident, __VARIABLE_PLACEHOLDER__);
        placeHolderType = type;
        libInvariant = SpecCompilerUtils.injectHeap(SpecCompilerUtils.HeapType.HEAP_H, visit(ctx.expressionStatement()).output);
        env.removeVariable(ident);
        return new SMLExpr("boolean", libInvariant);
    }*/

/*	@Override public SMLExpr visitSpecObservesInvariantFor(SolidityParser.SpecObservesInvariantForContext ctx) {
        // We assume that there is only one lib invariant, no need to parse second identifier
        SMLExpr ident = visit(ctx.identifier());
        return ;
    }*/

    @Override public SMLExpr visitArrayAccessExpression(SolidityParser.ArrayAccessExpressionContext ctx) {
        //dont forget implicit this/self
        SMLExpr r1 = visit(ctx.expression(0));
        SMLExpr r2 = visit(ctx.expression(1));
        String type = r1.type.substring(0,r1.type.length()-2);
        String intCast = !("int").equals(r2.type) ? "(int)" : "";
        String res = "(" + type + 
            "::select(" + SpecCompilerUtils.HEAP_PLACEHOLDER_STRING + "," + r1.output + ", arr(" + intCast +  r2.output + ")))"; 
        return new SMLExpr(type,res);
    }

    @Override public SMLExpr visitNumberLiteral(SolidityParser.NumberLiteralContext ctx) {
        return new SMLExpr("int", ctx.DecimalNumber().getText());
    }
    
    @Override public SMLExpr visitIdentifier(SolidityParser.IdentifierContext ctx) { 
        String ident = ctx.Identifier() != null ? ctx.Identifier().getText() : ctx.getText();
        String type = env.funcs.get(function).parameters.get(ident);
        if (type != null) { // identifier is function parameter
            return new SMLExpr(type, ident);
        } else if (ident.equals("this")) {
            return new SMLExpr("","this");
        } else {
            if (env.enums.contains(ident) || env.enums.contains(env.vars.get(ident))) {
                type = contractNameInPOs + "." + (env.enums.contains(ident) ? ident : env.vars.get(ident));
                enumToKeYType.put(ident, type);
            } else {
                type = env.vars.get(ident);
            }
            if (type.equals(__VARIABLE_PLACEHOLDER__)) {
                return new SMLExpr(placeHolderType, __VARIABLE_PLACEHOLDER__);
            }
            String access = !type.equals("logical") ? 
                "(" + type + "::select(" + SpecCompilerUtils.HEAP_PLACEHOLDER_STRING + ",self," +
                injectFieldPrefix(ident) + "))" :
                ident;
            return new SMLExpr(type, access);
        }
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
        String logicalVarType = SpecCompilerUtils.solidityToJavaType(ctx.typeName().getText());
        env.cumulativeLogicalVars.put(ctx.Identifier().getText(), logicalVarType);
        env.addVariable(ctx.Identifier().getText(), "logical");
        SMLExpr r = visit(ctx.expression());
        SMLExpr ret = new SMLExpr(r.type, "(\\forall " + 
            (stmtType == SMLStatementType.ON_SUCCESS ? logicalVarType + " ": "") + 
            ctx.Identifier().getText() + "; " + 
            r.output + ")");
        env.removeVariable(ctx.Identifier().getText());
        return ret;
    }

    @Override public SMLExpr visitExistsExpression(SolidityParser.ExistsExpressionContext ctx) {
        String logicalVarType = SpecCompilerUtils.solidityToJavaType(ctx.typeName().getText());
        env.cumulativeLogicalVars.put(ctx.Identifier().getText(), logicalVarType);
        env.addVariable(ctx.Identifier().getText(), "logical");
        SMLExpr r = visit(ctx.expression());
        SMLExpr ret = new SMLExpr(r.type, "(\\exists " + 
            (stmtType == SMLStatementType.ON_SUCCESS ? logicalVarType + " ": "") + 
            ctx.Identifier().getText() + "; " + 
            r.output + ")");
        env.removeVariable(ctx.Identifier().getText());
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
        pos.setGross(function, true);
        SMLExpr r = visit(ctx.expression());
        return returnFromNetGross(r, "gross_to");
    }

	@Override public SMLExpr visitGrossFromExpression(SolidityParser.GrossFromExpressionContext ctx) { 
        pos.setGross(function, true);
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

// parameter
//p :: Outer.Inner            can get type, output
//p.member :: e.g. int        cac get type, output if "p." in front. t::select(heap, _placeholder_, outer.inner::$member)

// var in lib invariant

//int::select(heap, ArrTest.InnerClass::select(heap, self_25, ArrTest::$c), ArrTest.InnerClass::$a)
//int::select(heap, __VAR_PLACEHOLDER_STRING__, ArrTest.InnerClass::$a)

//assumption generation


	@Override public SMLExpr visitDotExpression(SolidityParser.DotExpressionContext ctx) {
        SMLExpr r = visit(ctx.expression());
        String ident = ctx.identifier().Identifier().getText();
        String type = null;
        String output = null;
//        System.out.println(r.type);
//        System.out.println(env.userTypes.entrySet());
        if (enumToKeYType.containsValue(r.type)) {
            type = r.type;
            output = r.type + "::select(" + SpecCompilerUtils.HEAP_PLACEHOLDER_STRING + ",null," + r.type + "::$" + ident + ")";
        } else if (ident.equals("length") || ident.equals("arr_length")) {
            type = "int";
            output = "(" + "int" + "::select(" + SpecCompilerUtils.HEAP_PLACEHOLDER_STRING + "," + r.output + "," + ident + "))";
        } else if (r.type.equals("Message")) {    // assuming either msg.sender or msg.value
            type = ident.equals("sender") ? "Address" : "int";
            output = "(" + type + "::select(" + SpecCompilerUtils.HEAP_PLACEHOLDER_STRING + ",msg,java.lang.Message::$" + ident + "))";
        } else if (r.output.equals("this") && ident.equals("balance")) {
            type = env.vars.get(ident); 
            output = "(" + type + "::select(" + SpecCompilerUtils.HEAP_PLACEHOLDER_STRING + ",self,java.lang.Address::$" + ident + "))";
        } else if (env.userTypes.containsKey(r.type)) {
            type = env.userTypes.get(r.type).members.get(ident);
            output = "(" + type + "::select(" + SpecCompilerUtils.HEAP_PLACEHOLDER_STRING + "," + r.output + ","  + r.type + "::$" + ident + "))";
        } else {
            throw new RuntimeException("unsupported expression in dot expression");
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
        String type = env.funcs.get(function).returnType;
        if (type == null) {
            throw new IllegalArgumentException("Referring to result of a void function");
        }
        return new SMLExpr(type, "_result");
    }

    // this was implemented somewhat arbitrarily, don't know if it should be changed
    @Override public SMLExpr aggregateResult(SMLExpr agg, SMLExpr next) {
        if (agg == null) {
            return next;
        } else if (next == null) {
            return agg;
        } else {
            return next;
        }
    }

    public String injectFieldPrefix(String str) {
        if (str.equals("balance")) 
            return "java.lang.Address::$balance";
        return contractNameInPOs + "::$" + str;
    }

}
