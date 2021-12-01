package org.key_project.java;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.proof.init.JavaProfile;
import org.antlr.v4.runtime.CharStreams;
import recoder.ParserException;
import recoder.java.*;
import recoder.java.declaration.TypeArgumentDeclaration;
import recoder.java.declaration.TypeParameterDeclaration;
import recoder.java.declaration.VariableDeclaration;
import recoder.java.expression.Literal;
import recoder.java.expression.Operator;
import recoder.java.expression.literal.*;
import recoder.java.expression.operator.*;
import recoder.java.reference.*;
import recoder.java.statement.*;
import recoder.list.generic.ASTList;

import java.io.IOException;
import java.io.StringReader;
import java.math.BigInteger;

import static org.key_project.java.JavaSorts.JAVA_CATCH;
import static org.key_project.java.JavaSorts.JAVA_STATEMENT;

/**
 * @author Alexander Weigl
 * @version 1 (11/25/21)
 */
public class Test {
    private static String input =
            "{ int x = 2;\n" +
                    " x++; \n" +
                    "y = 2*x; \n" +
                    "if(x < (++y) ) { z = 2; } \n" +
                    "else { y= x+z; } }";

    static Services services = new Services(JavaProfile.getDefaultProfile());
    static JavaOperators jops;
    static TermFactory tf = services.getTermFactory();
    static TermBuilder tb = services.getTermBuilder();

    public static void main(String[] args) throws ParserException, IOException {
        KeyIO io = new KeyIO(services);
        io.load(CharStreams.fromFileName("key.core/src/main/resources/de/uka/ilkd/key/proof/rules/boolean.key"))
                .parseFile()
                .loadDeclarations()
                .loadSndDegreeDeclarations();
        io.load(CharStreams.fromFileName("key.core/src/main/resources/de/uka/ilkd/key/proof/rules/integerHeader.key"))
                .parseFile()
                .loadDeclarations().loadSndDegreeDeclarations();

        jops = new JavaOperators(services.getNamespaces());
        JavaProgramFactory jpf = JavaProgramFactory.getInstance();
        StatementBlock stmts = jpf.parseStatementBlock(new StringReader(input));
        Term t = translate(stmts);
        System.out.println(t);
    }

    private static Term translate(JavaSourceElement element) {
        MV mv = new MV();
        element.accept(mv);
        return mv.term;
    }

    static class MV extends SourceVisitor {
        public Term term;

        @Override
        public void visitStatementBlock(StatementBlock x) {
            var op = jops.Sequential;
            if (x.getChildCount() == 0) {
                term = tf.createTerm(jops.EmptyExpr);
                wrapToStatement();
            } else if (x.getChildCount() == 1) {
                x.getChildAt(0).accept(this);
                wrapToStatement();
            } else {
                x.getChildAt(x.getChildCount() - 1).accept(this);
                wrapToStatement();
                for (int i = x.getChildCount() - 2; i >= 0; i--) {
                    Term rest = term;
                    term = null;
                    x.getChildAt(i).accept(this);
                    wrapToStatement();
                    term = tf.createTerm(op, term, rest);
                }
            }
        }

        private void wrapToStatement() {
            if (term.sort() == JavaSorts.JAVA_EXPR) {
                term = tf.createTerm(jops.ExpressionStmt, term);
            }
        }

        @Override
        public void visitTypeReference(TypeReference x) {
            Function varOp = new Function(new Name(x.getName()), JavaSorts.JAVA_NAME);
            term = tf.createTerm(varOp);
            term = tf.createTerm(jops.TypeExpr, term);
        }

        @Override
        public void visitVariableDeclaration(VariableDeclaration x) {
            x.getTypeReference().accept(this);
            Term type = term;
            var variable = x.getVariables().get(0);
            Function varOp = new Function(new Name(variable.getName()), JavaSorts.JAVA_NAME);
            var v = tf.createTerm(varOp);
            if (variable.getInitializer() != null) {
                variable.getInitializer().accept(this);
            } else {
                term = tf.createTerm(jops.EmptyExpr);
            }

            term = tf.createTerm(jops.VariableDeclarationExpr, type, v, term);
        }

        @Override
        public void visitCopyAssignment(CopyAssignment x) {
            binary(jops.AssignExpr, x);
        }

        @Override
        public void visitTimes(Times x) {
            binary(jops.BinaryMultExpr, x);
        }

        private void unary(Function op, Operator x) {
            x.getChildAt(0).accept(this);
            term = tf.createTerm(op, term);
        }

        private void binary(Function op, Operator x) {
            x.getChildAt(0).accept(this);
            var left = term;
            x.getChildAt(1).accept(this);
            term = tf.createTerm(op, left, term);
        }

        @Override
        public void visitPlus(Plus x) {
            binary(jops.BinaryAddExpr, x);
        }

        @Override
        public void visitDivide(Divide x) {
            binary(jops.BinaryDivExpr, x);
        }

        @Override
        public void visitModulo(Modulo x) {
            binary(jops.BinaryModExpr, x);
        }

        @Override
        public void visitBinaryAnd(BinaryAnd x) {
            binary(jops.BinaryAndExpr, x);
        }

        @Override
        public void visitBinaryNot(BinaryNot x) {
            unary(jops.UnaryExprBitwiseNegation, x);
        }


        @Override
        public void visitBinaryOr(BinaryOr x) {
            binary(jops.BinaryOrExpr, x);
        }

        @Override
        public void visitBinaryXOr(BinaryXOr x) {
            binary(jops.BinaryXorExpr, x);
        }

        @Override
        public void visitIntLiteral(IntLiteral x) {
            term = toZNotation(x.getValue(), services.getNamespaces().functions());
            term = tf.createTerm(jops.IntegerLiteralExpr, term);
        }

        @Override
        public void visitPostIncrement(PostIncrement x) {
            x.getChildAt(0).accept(this);
            term = tf.createTerm(jops.PostIncrement, term);
        }

        @Override
        public void visitUncollatedReferenceQualifier(UncollatedReferenceQualifier x) {
            Function varOp = new Function(new Name(x.getName()), JavaSorts.JAVA_EXPR);
            var variable = tf.createTerm(varOp);
            term = tf.createTerm(jops.NameExpr, variable);
        }

        @Override
        public void visitBooleanLiteral(BooleanLiteral x) {
            term = tf.createTerm(jops.BooleanLiteralExpr, x.getValue() ? tb.TRUE() : tb.FALSE());
        }


        @Override
        public void visitCharLiteral(CharLiteral x) {
            super.visitCharLiteral(x);
        }

        @Override
        public void visitDoubleLiteral(DoubleLiteral x) {
            term = tf.createTerm(jops.DoubleLiteralExpr /*,todo*/);
        }

        @Override
        public void visitFloatLiteral(FloatLiteral x) {
            term = tf.createTerm(jops.DoubleLiteralExpr /*,todo*/);
        }

        @Override
        public void visitLongLiteral(LongLiteral x) {
            term = tf.createTerm(jops.LongLiteralExpr, tb.zTerm(x.getValue()));
        }

        @Override
        public void visitNullLiteral(NullLiteral x) {
            term = tf.createTerm(jops.NullLiteralExpr);
        }

        @Override
        public void visitStringLiteral(StringLiteral x) {
            super.visitStringLiteral(x);
        }

        @Override
        public void visitBinaryAndAssignment(BinaryAndAssignment x) {
            super.visitBinaryAndAssignment(x);
        }

        @Override
        public void visitBinaryOrAssignment(BinaryOrAssignment x) {
            super.visitBinaryOrAssignment(x);
        }

        @Override
        public void visitBinaryXOrAssignment(BinaryXOrAssignment x) {
            super.visitBinaryXOrAssignment(x);
        }

        @Override
        public void visitConditional(Conditional x) {
            x.getChildAt(0);
            var a = term;

            x.getChildAt(1);
            var b = term;

            x.getChildAt(2);
            term = tf.createTerm(jops.ConditionalExpr, a, b, term);
        }

        @Override
        public void visitDivideAssignment(DivideAssignment x) {
            super.visitDivideAssignment(x);
        }

        @Override
        public void visitEquals(Equals x) {
            binary(jops.EqualsExpr, x);
        }

        @Override
        public void visitGreaterOrEquals(GreaterOrEquals x) {
            binary(jops.GTEExpr, x);
        }

        @Override
        public void visitGreaterThan(GreaterThan x) {
            binary(jops.GTExpr, x);
        }

        @Override
        public void visitInstanceof(Instanceof x) {
            binary(jops.InstanceOfExpr, x);
        }

        @Override
        public void visitLessOrEquals(LessOrEquals x) {
            binary(jops.LTEExpr, x);
        }

        @Override
        public void visitLessThan(LessThan x) {
            binary(jops.LTExpr, x);
        }

        @Override
        public void visitLogicalAnd(LogicalAnd x) {
            binary(jops.LogicalAndExpr, x);
        }

        @Override
        public void visitLogicalNot(LogicalNot x) {
            unary(jops.UnaryExprLogicalNegation, x);
        }

        @Override
        public void visitLogicalOr(LogicalOr x) {
            binary(jops.LogicalOrExpr, x);
        }

        @Override
        public void visitMinus(Minus x) {
            binary(jops.UnaryExprMinus, x);
        }

        @Override
        public void visitMinusAssignment(MinusAssignment x) {
            super.visitMinusAssignment(x);
        }

        @Override
        public void visitModuloAssignment(ModuloAssignment x) {
            super.visitModuloAssignment(x);
        }

        @Override
        public void visitNegative(Negative x) {
            unary(jops.UnaryExprBitwiseNegation, x);
        }

        @Override
        public void visitNew(New x) {
            createExpressionList(x.getArguments());
            var args = term;

            assert false; //TODO where is the class name?
            var name = term;
            term = tf.createTerm(jops.ObjectCreationExpr, name, args);
        }


        @Override
        public void visitNewArray(NewArray x) {
            assert false;
            var type = term;

            var dimension = term;

            Term init = tf.createTerm(jops.EmptyExpr);
            if (x.getArrayInitializer() != null) {
                x.getArrayInitializer().accept(this);
                init = term;
            }

            term = tf.createTerm(jops.ArrayCreationExpr, type, dimension, init);
        }

        @Override
        public void visitNotEquals(NotEquals x) {
            binary(jops.NotEqualsExpr, x);
        }

        @Override
        public void visitPlusAssignment(PlusAssignment x) {
            binary(jops.AssignAddExpr, x);

        }

        @Override
        public void visitPositive(Positive x) {
            super.visitPositive(x);
        }

        @Override
        public void visitPostDecrement(PostDecrement x) {
            unary(jops.PostDecrement, x);
        }

        @Override
        public void visitPreDecrement(PreDecrement x) {
            unary(jops.PreDecrement, x);
        }

        @Override
        public void visitPreIncrement(PreIncrement x) {
            unary(jops.PreIncrement, x);
        }

        @Override
        public void visitShiftLeft(ShiftLeft x) {
            binary(jops.ShiftLeftExpr, x);
        }

        @Override
        public void visitShiftLeftAssignment(ShiftLeftAssignment x) {
            binary(jops.ShiftLeftAssignExpr, x);
        }

        @Override
        public void visitShiftRight(ShiftRight x) {
            binary(jops.ShiftRightExpr, x);

        }

        @Override
        public void visitShiftRightAssignment(ShiftRightAssignment x) {
            binary(jops.ShiftRightAssignExpr, x);
        }

        @Override
        public void visitTimesAssignment(TimesAssignment x) {
            binary(jops.MultiAssignExpr, x);
        }

        @Override
        public void visitTypeCast(TypeCast x) {
            binary(jops.CastExpr, x);
        }

        @Override
        public void visitUnsignedShiftRight(UnsignedShiftRight x) {
            binary(jops.UnsignedShiftRightExpr, x);
        }

        @Override
        public void visitUnsignedShiftRightAssignment(UnsignedShiftRightAssignment x) {
            binary(jops.UnsignedShiftRightAssignExpr, x);
        }

        @Override
        public void visitBreak(Break x) {
            if (x.getChildCount() == 0)
                term = tf.createTerm(jops.EmptyName);
            else
                x.getChildAt(0).accept(this);

            term = tf.createTerm(jops.BreakStmt, term);
        }

        @Override
        public void visitCase(Case x) {
            super.visitCase(x);
        }

        @Override
        public void visitCatch(Catch x) {
            super.visitCatch(x);
        }

        @Override
        public void visitContinue(Continue x) {
            if (x.getChildCount() == 0)
                term = tf.createTerm(jops.EmptyName);
            else
                x.getChildAt(0).accept(this);

            term = tf.createTerm(jops.ContinueStmt, term);
        }

        @Override
        public void visitDefault(Default x) {
            super.visitDefault(x);
        }

        @Override
        public void visitDo(Do x) {
            x.getGuard().accept(this);
            var cond = term;
            x.getBody().accept(this);
            var body = term;
            term = tf.createTerm(jops.DoStmt, cond, body);
        }

        @Override
        public void visitElse(Else x) {
            super.visitElse(x);
        }

        @Override
        public void visitEmptyStatement(EmptyStatement x) {
            term = tf.createTerm(jops.EmptyStmt);
        }

        @Override
        public void visitFinally(Finally x) {
            super.visitFinally(x);
        }

        @Override
        public void visitFor(For x) {
            super.visitFor(x);
        }

        @Override
        public void visitEnhancedFor(EnhancedFor x) {
            super.visitEnhancedFor(x);
        }

        @Override
        public void visitAssert(Assert x) {
            x.getCondition().accept(this);
            var cond = term;
            term = tf.createTerm(jops.AssertStmt, cond);
        }

        @Override
        public void visitIf(If x) {
            x.getExpression().accept(this);
            var cond = term;
            x.getThen().getBody().accept(this);
            var body = term;
            x.getElse().getBody().accept(this);
            var _else = term;
            term = tf.createTerm(jops.IfStmt, cond, body, _else);
        }

        @Override
        public void visitLabeledStatement(LabeledStatement x) {
            createNameExpr(x.getName());
            var cond = term;
            x.getBody().accept(this);
            var body = term;
            term = tf.createTerm(jops.IfStmt, cond, body);
        }

        private void createNameExpr(String name) {
            Function varOp = new Function(new Name(name), JavaSorts.JAVA_NAME);
            term = tf.createTerm(varOp);
        }

        @Override
        public void visitReturn(Return x) {
            x.getExpression().accept(this);
            term = tf.createTerm(jops.ReturnStmt, term);
        }

        @Override
        public void visitSwitch(Switch x) {
            super.visitSwitch(x);
        }

        @Override
        public void visitSynchronizedBlock(SynchronizedBlock x) {
            x.getExpression().accept(this);
            var cond = term;
            x.getBody().accept(this);
            var body = term;
            term = tf.createTerm(jops.SynchronizedStmt, cond, body);
        }

        @Override
        public void visitThrow(Throw x) {
            x.getExpression().accept(this);
            term = tf.createTerm(jops.ThrowStmt, term);
        }

        @Override
        public void visitTry(Try x) {
            x.getBody().accept(this);
            var body = term;
            term = null;
            createCatchClauses(x.getBranchList());
            var catc = term;

            Term finBody;
            if(hasFinally(x.)) {

            }else{
                finBody = tf.createTerm(jops.EmptyStmt);
            }

            TryStmt = createJavaStatement("Try", JAVA_STATEMENT, JAVA_CATCH, JAVA_STATEMENT);

            term = tf.createTerm(jops.TryStmt, body, catc, finBody)
        }

        private void createCatchClauses(ASTList<Branch> branchList) {

        }

        @Override
        public void visitWhile(While x) {
            x.getGuard().accept(this);
            var cond = term;
            x.getBody().accept(this);
            var body = term;
            term = tf.createTerm(jops.WhileStmt, cond, body);
        }

        @Override
        public void visitArrayReference(ArrayReference x) {
            super.visitArrayReference(x);
        }

        @Override
        public void visitArrayLengthReference(ArrayLengthReference x) {
            super.visitArrayLengthReference(x);
        }

        @Override
        public void visitFieldReference(FieldReference x) {
            super.visitFieldReference(x);
        }

        @Override
        public void visitMetaClassReference(MetaClassReference x) {
            super.visitMetaClassReference(x);
        }

        @Override
        public void visitMethodReference(MethodReference x) {
            super.visitMethodReference(x);
        }

        @Override
        public void visitPackageReference(PackageReference x) {
            super.visitPackageReference(x);
        }

        @Override
        public void visitSuperConstructorReference(SuperConstructorReference x) {
            createExpressionList(x);
            term = tf.createTerm(jops.superConstructorInvocationStmt, term);
        }

        private void createExpressionList(ASTList<Expression> x) {
            for (int i = x.size() - 1; i >= 0; i--) {
                Term last = term;
                x.get(i).accept(this);
                term = tf.createTerm(jops.CommaExpr, term, last);
            }
        }

        private void createExpressionList(ExpressionContainer x) {
            for (int i = x.getExpressionCount() - 1; i >= 0; i--) {
                Term last = term;
                x.getExpressionAt(i).accept(this);
                term = tf.createTerm(jops.CommaExpr, term, last);
            }
        }

        @Override
        public void visitSuperReference(SuperReference x) {
            term = tf.createTerm(jops.SuperExpr);
        }

        @Override
        public void visitThisConstructorReference(ThisConstructorReference x) {
            createExpressionList(x);
            term = tf.createTerm(jops.thisConstructorInvocationStmt);
        }

        @Override
        public void visitThisReference(ThisReference x) {
            term = tf.createTerm(jops.ThisExpr);
        }

        @Override
        public void visitVariableReference(VariableReference x) {
            super.visitVariableReference(x);
        }

        @Override
        protected void visitLiteral(Literal x) {
            assert false;
        }

        @Override
        protected void visitOperator(Operator x) {
            assert false;
        }


        @Override
        public void visitTypeArgument(TypeArgumentDeclaration x) {
            super.visitTypeArgument(x);
        }

        @Override
        public void visitTypeParameter(TypeParameterDeclaration x) {
            super.visitTypeParameter(x);
        }

        private Term toZNotation(String literal, Namespace<Function> functions) {
            literal = literal.replace("_", "");
            final boolean negative = (literal.charAt(0) == '-');
            if (negative) {
                literal = literal.substring(1);
            }
            int base = 10;

            if (literal.startsWith("0x")) {
                literal = literal.substring(2);
                base = 16;
            }

            if (literal.startsWith("0b")) {
                literal = literal.substring(2);
                base = 8;
            }

            BigInteger bi = new BigInteger(literal, base);
            return toZNotation(bi, functions);
        }

        private Term toZNotation(BigInteger bi, Namespace<Function> functions) {
            boolean negative = bi.signum() < 0;
            String s = bi.abs().toString();
            Term result = tf
                    .createTerm(functions.lookup(new Name("#")));

            for (int i = 0; i < s.length(); i++)
                result = tf.createTerm(
                        functions.lookup(new Name(s.substring(i, i + 1))), result);

            if (negative) {
                result = tf.createTerm(
                        functions.lookup(new Name("neglit")), result);
            }
            return tf.createTerm(
                    functions.lookup(new Name("Z")), result);
        }

    }
}
