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

class SMLExpr {
    String type; String output;
    SMLExpr(String t, String o) {
        type = t; output = o;
    }
    public String toString() {
        return type + " " + output;
    }
}

public class SoliditySpecVisitor extends SolidityBaseVisitor<SMLExpr> {

    private Environment env;
    
    public String invariant;
    public FunctionProofObligations pos = new FunctionProofObligations();

    private String contractName;
    private String function;

    public SoliditySpecVisitor(String contractName, String function, Environment env) {
        super();
        this.contractName = contractName;
        this.function = function;
        this.env = env;
    }

    @Override public SMLExpr visitSpecOnlyIf(SolidityParser.SpecOnlyIfContext ctx) {
        SMLExpr r = visitChildren(ctx);
        r.output = SpecCompilerUtils.injectHeap(SpecCompilerUtils.HeapType.OLD_HEAP, r.output);
        pos.onlyIf = r.output;
        return r;
    }

    @Override public SMLExpr visitSpecAssumes(SolidityParser.SpecAssumesContext ctx) { return visitChildren(ctx); }

	@Override public SMLExpr visitSpecAssignable(SolidityParser.SpecAssignableContext ctx) {
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
            r.output = r.output.substring(r.output.indexOf(SpecCompilerUtils.HEAP_PLACEHOLDER_STRING)+SpecCompilerUtils.HEAP_PLACEHOLDER_STRING.length()+1);
            r.output = r.output.substring(0,r.output.length()-numParentheses); // remove trailing parentheses 
            pos.assignable.add(r.output);
        }
        return new SMLExpr("","");
    }

    @Override public SMLExpr visitSpecOnSuccess(SolidityParser.SpecOnSuccessContext ctx) { 
        SMLExpr r = visitChildren(ctx);
        r.output = SpecCompilerUtils.injectHeap(SpecCompilerUtils.HeapType.HEAP, r.output);
        pos.onSuccess = r.output;
        return r;
    }

    @Override public SMLExpr visitSpecClassInvariant(SolidityParser.SpecClassInvariantContext ctx) {
        SMLExpr r = visitChildren(ctx);
        invariant = SpecCompilerUtils.injectHeap(SpecCompilerUtils.HeapType.HEAP_H, r.output); // assuming only one invariant per contract
        r.output = invariant;
        return r;
    }

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
        } else {
            if (ident.equals("this")) {
                return new SMLExpr("","this");
            }
            type = env.vars.get(ident);
            if (("enum").equals(env.vars.get(type))) {
                type = contractName + "." + type;
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
        env.cumulativeLogicalVars.put(ctx.Identifier().getText(), SpecCompilerUtils.solidityToJavaType(ctx.typeName().getText()));
        env.vars.put(ctx.Identifier().getText(), "logical");
        SMLExpr r = visit(ctx.expression());
        SMLExpr ret = new SMLExpr(r.type, "(\\forall " + 
            ctx.Identifier().getText() + "; " + 
            r.output + ")");
        env.vars.remove(ctx.Identifier().getText());
        return ret;
    }

    @Override public SMLExpr visitExistsExpression(SolidityParser.ExistsExpressionContext ctx) {
        env.cumulativeLogicalVars.put(ctx.Identifier().getText(), SpecCompilerUtils.solidityToJavaType(ctx.typeName().getText()));
        env.vars.put(ctx.Identifier().getText(), "logical");
        SMLExpr r = visit(ctx.expression());
        SMLExpr ret = new SMLExpr(r.type, "(\\exists " + 
            ctx.Identifier().getText() + "; " + 
            r.output + ")");
        env.vars.remove(ctx.Identifier().getText());
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
        pos.isGross = true;
        SMLExpr r = visit(ctx.expression());
        return returnFromNetGross(r, "gross_to");
    }

	@Override public SMLExpr visitGrossFromExpression(SolidityParser.GrossFromExpressionContext ctx) { 
        pos.isGross = true;
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
        SMLExpr r = visit(ctx.expression());
        String ident = ctx.identifier().Identifier().getText();
        String typeOutput = contractName + "." + ctx.expression().getText();
        String type = null;
        String output = null;
        if (r.type.equals("enum")) {
            type = r.type;
            output = typeOutput + "::select(" + SpecCompilerUtils.HEAP_PLACEHOLDER_STRING + ",null," + typeOutput + "::$" + ident + ")";
        } else if (ident.equals("length") || ident.equals("arr_length")) {
            type = "int";
            output = "(" + "int" + "::select(" + SpecCompilerUtils.HEAP_PLACEHOLDER_STRING + "," + r.output + "," + ident + "))";
            
        } else if (r.type.equals("Message")) {    // assuming either msg.sender or msg.value
            type = ident.equals("sender") ? "Address" : "int";
            output = "(" + type + "::select(" + SpecCompilerUtils.HEAP_PLACEHOLDER_STRING + ",msg,java.lang.Message::$" + ident + "))";
        } else if (r.output.equals("this") && ident.equals("balance")) {
            type = env.vars.get(ident); 
            output = "(" + type + "::select(" + SpecCompilerUtils.HEAP_PLACEHOLDER_STRING + ",self,java.lang.Address::$" + ident + "))";
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
        return contractName + "::$" + str;
    }

}
