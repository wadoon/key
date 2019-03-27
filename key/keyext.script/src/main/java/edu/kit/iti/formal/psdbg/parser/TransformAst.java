package edu.kit.iti.formal.psdbg.parser;

/*-
 * #%L
 * ProofScriptParser
 * %%
 * Copyright (C) 2017 Application-oriented Formal Verification
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */


import edu.kit.iti.formal.psdbg.parser.ast.*;
import edu.kit.iti.formal.psdbg.parser.function.FunctionRegister;
import edu.kit.iti.formal.psdbg.parser.function.ScriptFunction;
import edu.kit.iti.formal.psdbg.parser.types.TypeFacade;
import lombok.Getter;
import lombok.Setter;
import lombok.val;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ErrorNode;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.RuleNode;
import org.antlr.v4.runtime.tree.TerminalNode;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 2 (29.10.17), introduction of parent
 * version 1 (27.04.17)
 */
public class TransformAst implements ScriptLanguageVisitor<Object> {
    /**
     * Start index for positional arguments for command calls
     */
    public static final int KEY_START_INDEX_PARAMETER = 2;

    @Getter
    private final List<ProofScript> scripts = new ArrayList<>(10);

    @Getter
    @Setter
    private FunctionRegister functionRegister = FunctionRegister.getDefault();

    private Function<String, UnconditionalBlock> ubFactory;

    private Function<String, ConditionalBlock> cbFactory;


    public TransformAst() {
        functionRegister.loadDefault();
        ubFactory = (id -> {
            switch (id) {
                case "foreach":
                    return new ForeachStatement();
                case "theonly":
                    return new TheOnlyStatement();
                case "repeat":
                    return new RepeatStatement();
                case "relax":
                    return new RelaxBlock();
                case "strict":
                    return new StrictBlock();
                default:
                    throw new RuntimeException("Block " + id + " is not known.");
            }
        });

        cbFactory = (id -> {
            switch (id) {
                case "if":
                    return new IfStatement();
                case "while":
                    return new WhileStatement();
                default:
                    throw new RuntimeException("Block " + id + " is not known.");
            }
        });
    }

    @Override
    public List<ProofScript> visitStart(ScriptLanguageParser.StartContext ctx) {
        ctx.script().forEach(s ->
                scripts.add((ProofScript) s.accept(this)));
        return scripts;
    }

    @Override
    public ProofScript visitScript(ScriptLanguageParser.ScriptContext ctx) {
        ProofScript s = new ProofScript();
        s.setName(ctx.name.getText());
        s.setRuleContext(ctx);
        if (ctx.signature != null) {
            final Signature sig = (Signature) ctx.signature.accept(this);
            sig.setParent(s);
            s.setSignature(sig);
        }
        s.setBody((Statements) ctx.body.accept(this));
        s.getBody().setParent(s);
        return s;
    }

    @Override
    public Signature visitArgList(ScriptLanguageParser.ArgListContext ctx) {
        Signature signature = new Signature();
        signature.setRuleContext(ctx);
        for (ScriptLanguageParser.VarDeclContext decl : ctx.varDecl()) {
            Variable key = new Variable(decl.name);
            key.setParent(signature);
            signature.put(key, TypeFacade.findType(decl.type.getText()));
        }
        return signature;
    }

    /**
     * @param ctx the parse tree
     * @return
     * @deprecated not needed, handled in {@link #visitArgList(ScriptLanguageParser.ArgListContext)}
     */
    @Override
    public Object visitVarDecl(ScriptLanguageParser.VarDeclContext ctx) {
       /* VariableDeclaration varDecl = new VariableDeclaration();
        varDecl.setIdentifier(new Variable(ctx.name));
        varDecl.setType(SimpleType.findType(ctx.type.getText()));
        return varDecl;*/
        return null;

    }

    @Override
    public Statements visitStmtList(ScriptLanguageParser.StmtListContext ctx) {
        Statements statements = new Statements();
        statements.setRuleContext(ctx);
        for (ScriptLanguageParser.StatementContext stmt : ctx.statement()) {
            Statement<ParserRuleContext> statement = (Statement<ParserRuleContext>) stmt.accept(this);
            statement.setParent(statements);
            statements.add(statement);
        }
        return statements;
    }


    @Override
    public Object visitStatement(ScriptLanguageParser.StatementContext ctx) {
        return ctx.getChild(0).accept(this);
    }

    @Override
    public Object visitLetStmt(ScriptLanguageParser.LetStmtContext ctx) {
        LetStatement lst = new LetStatement();
        lst.setRuleContext(ctx);
        lst.setExpression((Expression) ctx.expression().accept(this));
        lst.getExpression().setParent(lst);
        if (ctx.statement() != null) {
            val stmt = (Statement) ctx.statement().accept(this);
            Statements stmts = new Statements();
            stmts.add(stmt);
            lst.setBody(stmts);
            stmts.setParent(lst);
        }
        if (ctx.stmtList() != null) {
            lst.setBody((Statements) ctx.stmtList().accept(this));
            lst.getBody().setParent(lst);
        }
        return lst;
    }

    @Override
    public Object visitAssignment(ScriptLanguageParser.AssignmentContext ctx) {
        AssignmentStatement assign = new AssignmentStatement();
        assign.setRuleContext(ctx);
        Variable lhs = new Variable(ctx.variable);
        lhs.setParent(assign);
        assign.setLhs(lhs);
        if (ctx.type != null) {
            assign.setType(TypeFacade.findType(ctx.type.getText()));
        }
        if (ctx.expression() != null) {
            Expression<ParserRuleContext> rhs = (Expression<ParserRuleContext>) ctx.expression().accept(this);
            rhs.setParent(assign);
            assign.setRhs(rhs);
        }
        return assign;
    }

    @Override
    public BinaryExpression visitExprMultiplication(ScriptLanguageParser.ExprMultiplicationContext ctx) {
        return createBinaryExpression(ctx, ctx.expression(), Operator.MULTIPLY);
    }

    private BinaryExpression createBinaryExpression(ParserRuleContext ctx,
                                                    List<ScriptLanguageParser.ExpressionContext> expression, Operator op) {
        Expression<ParserRuleContext> left = (Expression<ParserRuleContext>) expression.get(0).accept(this);
        Expression<ParserRuleContext> right = (Expression<ParserRuleContext>) expression.get(1).accept(this);
        BinaryExpression be = new BinaryExpression(left, op, right);
        left.setParent(be);
        right.setParent(be);
        return be;
    }

    @Override
    public Object visitExprNot(ScriptLanguageParser.ExprNotContext ctx) {
        return createUnaryExpression(ctx, ctx.expression(), Operator.NOT);
    }

    @Override
    public Object visitExprNegate(ScriptLanguageParser.ExprNegateContext ctx) {
        return createUnaryExpression(ctx, ctx.expression(), Operator.NEGATE);
    }

    private UnaryExpression createUnaryExpression(ParserRuleContext ctx, ScriptLanguageParser.ExpressionContext expression, Operator op) {
        UnaryExpression ue = new UnaryExpression();
        ue.setRuleContext(ctx);
        Expression<ParserRuleContext> expr = (Expression<ParserRuleContext>) expression.accept(this);
        expr.setParent(ue);
        ue.setExpression(expr);
        ue.setOperator(op);
        return ue;
    }

    @Override
    public Object visitExprComparison(ScriptLanguageParser.ExprComparisonContext ctx) {
        return createBinaryExpression(ctx, ctx.expression(), findOperator(ctx.op.getText()));
    }


    private Operator findOperator(String n) {
        return findOperator(n, 2);
    }

    private Operator findOperator(String n, int arity) {
        for (Operator op : Operator.values()) {
            if (op.symbol().equals(n) && op.arity() == arity)
                return op;
        }
        throw new IllegalStateException("Operator " + n + " not defined");
    }

    @Override
    public Object visitExprEquality(ScriptLanguageParser.ExprEqualityContext ctx) {
        return createBinaryExpression(ctx, ctx.expression(), findOperator(ctx.op.getText()));

    }

    @Override
    public Object visitExprMatch(ScriptLanguageParser.ExprMatchContext ctx) {
        return ctx.matchPattern().accept(this);
    }

    @Override
    public Object visitExprIMP(ScriptLanguageParser.ExprIMPContext ctx) {
        return createBinaryExpression(ctx, ctx.expression(), Operator.IMPLICATION);

    }

    @Override
    public Object visitExprParen(ScriptLanguageParser.ExprParenContext ctx) {
        return ctx.expression().accept(this);
    }

    @Override
    public Object visitExprOr(ScriptLanguageParser.ExprOrContext ctx) {
        return createBinaryExpression(ctx, ctx.expression(), Operator.OR);

    }

    @Override
    public Object visitExprLineOperators(ScriptLanguageParser.ExprLineOperatorsContext ctx) {
        return createBinaryExpression(ctx, ctx.expression(), findOperator(ctx.op.getText()));

    }

    @Override
    public FunctionCall visitFunction(ScriptLanguageParser.FunctionContext ctx) {
        List<Expression> args = ctx.expression().stream()
                .map(c -> (Expression) c.accept(this))
                .collect(Collectors.toList());
        ScriptFunction func = functionRegister.get(ctx.ID().getText());
        return new FunctionCall(func, args);
    }

    @Override
    public Object visitExprAnd(ScriptLanguageParser.ExprAndContext ctx) {
        return createBinaryExpression(ctx, ctx.expression(), Operator.AND);
    }

    @Override
    public Object visitExprLiterals(ScriptLanguageParser.ExprLiteralsContext ctx) {
        return ctx.literals().accept(this);
    }

    @Override
    public Object visitExprSubst(ScriptLanguageParser.ExprSubstContext ctx) {
        SubstituteExpression se = new SubstituteExpression();
        Expression expr = (Expression) ctx.expression().accept(this);
        Map<String, Expression> subs = (Map<String, Expression>) ctx.substExpressionList().accept(this);
        subs.values().forEach(e -> e.setParent(se));
        se.setSubstitution(subs);
        se.setSub(expr);
        expr.setParent(se);
        return se;
    }

    @Override
    public Object visitExprDivision(ScriptLanguageParser.ExprDivisionContext ctx) {
        return createBinaryExpression(ctx, ctx.expression(), Operator.DIVISION);
    }

    @Override
    public Map<String, Expression<ParserRuleContext>> visitSubstExpressionList(ScriptLanguageParser.SubstExpressionListContext ctx) {
        Map<String, Expression<ParserRuleContext>> map = new LinkedHashMap<>();
        for (int i = 0; i < ctx.scriptVar().size(); i++) {
            map.put(ctx.scriptVar(i).getText(),
                    (Expression<ParserRuleContext>) ctx.expression(i).accept(this));
        }
        return map;
    }

    @Override
    public Object visitLiteralID(ScriptLanguageParser.LiteralIDContext ctx) {
        return new Variable(ctx.ID().getSymbol());
    }

    @Override
    public Object visitLiteralDigits(ScriptLanguageParser.LiteralDigitsContext ctx) {
        return new IntegerLiteral(ctx.DIGITS().getSymbol());
    }

    @Override
    public Object visitLiteralTerm(ScriptLanguageParser.LiteralTermContext ctx) {
        return new TermLiteral(ctx.TERM_LITERAL().getSymbol());
    }

    @Override
    public Object visitLiteralString(ScriptLanguageParser.LiteralStringContext ctx) {
        return new StringLiteral(ctx.getText());
    }

    @Override
    public Object visitLiteralTrue(ScriptLanguageParser.LiteralTrueContext ctx) {
        return new BooleanLiteral(true, ctx.TRUE().getSymbol());
    }

    @Override
    public Object visitLiteralFalse(ScriptLanguageParser.LiteralFalseContext ctx) {
        return new BooleanLiteral(false, ctx.FALSE().getSymbol());
    }

    @Override
    public Object visitMatchPattern(ScriptLanguageParser.MatchPatternContext ctx) {
        MatchExpression match = new MatchExpression();
        match.setRuleContext(ctx);

        if (ctx.derivable != null) {
            match.setDerivable(true);
            Expression<ParserRuleContext> e = (Expression<ParserRuleContext>) ctx.derivableExpression.accept(this);
            e.setParent(match);
            match.setDerivableTerm(e);
        } else {
            Expression<ParserRuleContext> e = (Expression<ParserRuleContext>) ctx.pattern.accept(this);
            match.setPattern(e);
            e.setParent(match);
        }
        return match;
    }

    @Override
    public Object visitScriptVar(ScriptLanguageParser.ScriptVarContext ctx) {
        throw new IllegalStateException("not implemented");
    }

    @Override
    public Object visitCasesStmt(ScriptLanguageParser.CasesStmtContext ctx) {
        CasesStatement cases = new CasesStatement();
        ctx.casesList().forEach(c -> cases.getCases().add((CaseStatement) c.accept(this)));
        if (ctx.DEFAULT() != null) {
            DefaultCaseStatement defCase = new DefaultCaseStatement();
            defCase.setRuleContext(ctx.defList);
            Statements body = (Statements) ctx.defList.accept(this);
            body.setParent(defCase);
            defCase.setBody(body);
            cases.setDefCaseStmt(defCase);
            defCase.setParent(cases);
        }
        cases.setRuleContext(ctx);
        return cases;
    }

    @Override
    public Object visitCasesList(ScriptLanguageParser.CasesListContext ctx) {
        Statements accept = (Statements) ctx.body.accept(this);
        CaseStatement cs = null;
        if (ctx.TRY() != null) {
            cs = new TryCase();
        } else if (ctx.closesGuard != null) {
            cs = new ClosesCase();
            Statements closes = (Statements) ctx.closesGuard.accept(this);
            ((ClosesCase) cs).setClosesGuard(closes);
            closes.setParent(cs);
        } else {
            cs = new GuardedCaseStatement();
            Expression<ParserRuleContext> guard = (Expression<ParserRuleContext>) ctx.expression().accept(this);
            ((GuardedCaseStatement) cs).setGuard(guard);
        }

        cs.setBody(accept);
        accept.setParent(cs);
        cs.setRuleContext(ctx);
        return cs;

    }


    @Override
    public UnconditionalBlock visitUnconditionalBlock(ScriptLanguageParser.UnconditionalBlockContext ctx) {
        List<UnconditionalBlock> list = ctx.kind.stream().map(token -> ubFactory.apply(token.getText())).collect(Collectors.toList());
        UnconditionalBlock first = list.get(0);
        UnconditionalBlock last = list.stream().reduce((a, b) -> {
            b.setParent(a);
            a.getBody().add(b);
            return b;
        }).orElse(first);
        list.forEach(a -> a.setRuleContext(ctx));
        Statements body = (Statements) ctx.stmtList().accept(this);
        last.setBody(body);
        body.setParent(last);
        return first;
    }

    @Override
    public ConditionalBlock visitConditionalBlock(ScriptLanguageParser.ConditionalBlockContext ctx) {
        ConditionalBlock cb = cbFactory.apply(ctx.kind.getText());
        cb.setRuleContext(ctx);
        Statements body = (Statements) ctx.stmtList().accept(this);
        cb.setBody(body);
        body.setParent(cb);
        return cb;
    }


    @Override
    public Object visitScriptCommand(ScriptLanguageParser.ScriptCommandContext ctx) {
        CallStatement scs = new CallStatement();
        scs.setRuleContext(ctx);
        String commandName = ctx.cmd.getText();
        //Sonderfall für KeYs heap-simp macro
      /*  if (commandName.equals("heap_simp")) {
            commandName = "heap-simp";
        }*/
        scs.setCommand(commandName);
        if (ctx.parameters() != null) {
            Parameters parameters = (Parameters) ctx.parameters().accept(this);
            parameters.setParent(scs);
            scs.setParameters(parameters);
        }
        return scs;
    }

    @Override
    public Object visitParameters(ScriptLanguageParser.ParametersContext ctx) {
        Parameters params = new Parameters();

        int i = KEY_START_INDEX_PARAMETER;

        for (ScriptLanguageParser.ParameterContext pc : ctx.parameter()) {
            Expression expr = (Expression) pc.expr.accept(this);
            Variable key = pc.pname != null ? new Variable(pc.pname) : new Variable("#" + (i++));
            key.setParent(params);
            expr.setParent(params);
            params.put(key, expr);
        }
        return params;
    }

    @Override
    public Object visitParameter(ScriptLanguageParser.ParameterContext ctx) {
        throw new IllegalStateException("not implemented");
    }

    @Override
    public Object visit(ParseTree parseTree) {
        throw new IllegalStateException("not implemented");
    }

    @Override
    public Object visitChildren(RuleNode ruleNode) {
        throw new IllegalStateException("not implemented");
    }

    @Override
    public Object visitTerminal(TerminalNode terminalNode) {
        throw new IllegalStateException("not implemented");
    }

    @Override
    public Object visitErrorNode(ErrorNode errorNode) {
        throw new IllegalStateException("not implemented");
    }
}
