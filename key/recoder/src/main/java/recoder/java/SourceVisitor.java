package recoder.java;

import recoder.java.declaration.*;
import recoder.java.declaration.modifier.*;
import recoder.java.expression.*;
import recoder.java.expression.literal.*;
import recoder.java.expression.operator.*;
import recoder.java.reference.*;
import recoder.java.statement.*;

public abstract class SourceVisitor {
    public void visitCompilationUnit(CompilationUnit x) {
    }

    public void visitIdentifier(Identifier x) {
    }

    public void visitImport(Import x) {
    }

    public void visitPackageSpecification(PackageSpecification x) {
    }

    public void visitStatementBlock(StatementBlock x) {
    }

    public void visitClassDeclaration(ClassDeclaration x) {
    }

    public void visitAnnotationDeclaration(AnnotationDeclaration x) {
    }

    public void visitClassInitializer(ClassInitializer x) {
    }

    public void visitConstructorDeclaration(ConstructorDeclaration x) {
        visitMethodDeclaration(x);
    }

    public void visitExtends(Extends x) {
    }

    public void visitFieldDeclaration(FieldDeclaration x) {
        visitVariableDeclaration(x);
    }

    public void visitImplements(Implements x) {
    }

    public void visitInterfaceDeclaration(InterfaceDeclaration x) {
    }

    public void visitLocalVariableDeclaration(LocalVariableDeclaration x) {
        visitVariableDeclaration(x);
    }

    public void visitMethodDeclaration(MethodDeclaration x) {
    }

    public void visitAnnotationPropertyDeclaration(AnnotationPropertyDeclaration x) {
        visitMethodDeclaration(x);
    }

    public void visitAnnotationPropertyReference(AnnotationPropertyReference x) {
        Identifier id = x.getIdentifier();
        if (id != null)
            id.accept(this);
    }

    public void visitParameterDeclaration(ParameterDeclaration x) {
        visitVariableDeclaration(x);
    }

    public void visitThrows(Throws x) {
    }

    public void visitVariableSpecification(VariableSpecification x) {
    }

    public void visitFieldSpecification(FieldSpecification x) {
        visitVariableSpecification(x);
    }

    public void visitAbstract(Abstract x) {
        visitModifier(x);
    }

    public void visitFinal(Final x) {
        visitModifier(x);
    }

    public void visitNative(Native x) {
        visitModifier(x);
    }

    public void visitPrivate(Private x) {
        visitModifier(x);
    }

    public void visitProtected(Protected x) {
        visitModifier(x);
    }

    public void visitPublic(Public x) {
        visitModifier(x);
    }

    public void visitStatic(Static x) {
        visitModifier(x);
    }

    public void visitStrictFp(StrictFp x) {
        visitModifier(x);
    }

    public void visitSynchronized(Synchronized x) {
        visitModifier(x);
    }

    public void visitTransient(Transient x) {
        visitModifier(x);
    }

    public void visitVolatile(Volatile x) {
        visitModifier(x);
    }

    public void visitElementValuePair(AnnotationElementValuePair x) {
    }

    public void visitAnnotationUse(AnnotationUseSpecification a) {
        visitDeclarationSpecifier(a);
    }

    public void visitDeclarationSpecifier(DeclarationSpecifier x) {
    }

    public void visitArrayInitializer(ArrayInitializer x) {
    }

    public void visitElementValueArrayInitializer(ElementValueArrayInitializer x) {
    }

    public void visitParenthesizedExpression(ParenthesizedExpression x) {
    }

    public void visitBooleanLiteral(BooleanLiteral x) {
        visitLiteral(x);
    }

    public void visitCharLiteral(CharLiteral x) {
        visitLiteral(x);
    }

    public void visitDoubleLiteral(DoubleLiteral x) {
        visitLiteral(x);
    }

    public void visitFloatLiteral(FloatLiteral x) {
        visitLiteral(x);
    }

    public void visitIntLiteral(IntLiteral x) {
        visitLiteral(x);
    }

    public void visitLongLiteral(LongLiteral x) {
        visitLiteral(x);
    }

    public void visitNullLiteral(NullLiteral x) {
        visitLiteral(x);
    }

    public void visitStringLiteral(StringLiteral x) {
        visitLiteral(x);
    }

    public void visitBinaryAnd(BinaryAnd x) {
        visitOperator(x);
    }

    public void visitBinaryAndAssignment(BinaryAndAssignment x) {
        visitOperator(x);
    }

    public void visitBinaryNot(BinaryNot x) {
        visitOperator(x);
    }

    public void visitBinaryOr(BinaryOr x) {
        visitOperator(x);
    }

    public void visitBinaryOrAssignment(BinaryOrAssignment x) {
        visitOperator(x);
    }

    public void visitBinaryXOr(BinaryXOr x) {
        visitOperator(x);
    }

    public void visitBinaryXOrAssignment(BinaryXOrAssignment x) {
        visitOperator(x);
    }

    public void visitConditional(Conditional x) {
        visitOperator(x);
    }

    public void visitCopyAssignment(CopyAssignment x) {
        visitOperator(x);
    }

    public void visitDivide(Divide x) {
        visitOperator(x);
    }

    public void visitDivideAssignment(DivideAssignment x) {
        visitOperator(x);
    }

    public void visitEquals(Equals x) {
        visitOperator(x);
    }

    public void visitGreaterOrEquals(GreaterOrEquals x) {
        visitOperator(x);
    }

    public void visitGreaterThan(GreaterThan x) {
        visitOperator(x);
    }

    public void visitInstanceof(Instanceof x) {
        visitOperator(x);
    }

    public void visitLessOrEquals(LessOrEquals x) {
        visitOperator(x);
    }

    public void visitLessThan(LessThan x) {
        visitOperator(x);
    }

    public void visitLogicalAnd(LogicalAnd x) {
        visitOperator(x);
    }

    public void visitLogicalNot(LogicalNot x) {
        visitOperator(x);
    }

    public void visitLogicalOr(LogicalOr x) {
        visitOperator(x);
    }

    public void visitMinus(Minus x) {
        visitOperator(x);
    }

    public void visitMinusAssignment(MinusAssignment x) {
        visitOperator(x);
    }

    public void visitModulo(Modulo x) {
        visitOperator(x);
    }

    public void visitModuloAssignment(ModuloAssignment x) {
        visitOperator(x);
    }

    public void visitNegative(Negative x) {
        visitOperator(x);
    }

    public void visitNew(New x) {
        visitOperator(x);
    }

    public void visitNewArray(NewArray x) {
        visitOperator(x);
    }

    public void visitNotEquals(NotEquals x) {
        visitOperator(x);
    }

    public void visitPlus(Plus x) {
        visitOperator(x);
    }

    public void visitPlusAssignment(PlusAssignment x) {
        visitOperator(x);
    }

    public void visitPositive(Positive x) {
        visitOperator(x);
    }

    public void visitPostDecrement(PostDecrement x) {
        visitOperator(x);
    }

    public void visitPostIncrement(PostIncrement x) {
        visitOperator(x);
    }

    public void visitPreDecrement(PreDecrement x) {
        visitOperator(x);
    }

    public void visitPreIncrement(PreIncrement x) {
        visitOperator(x);
    }

    public void visitShiftLeft(ShiftLeft x) {
        visitOperator(x);
    }

    public void visitShiftLeftAssignment(ShiftLeftAssignment x) {
        visitOperator(x);
    }

    public void visitShiftRight(ShiftRight x) {
        visitOperator(x);
    }

    public void visitShiftRightAssignment(ShiftRightAssignment x) {
        visitOperator(x);
    }

    public void visitTimes(Times x) {
        visitOperator(x);
    }

    public void visitTimesAssignment(TimesAssignment x) {
        visitOperator(x);
    }

    public void visitTypeCast(TypeCast x) {
        visitOperator(x);
    }

    public void visitUnsignedShiftRight(UnsignedShiftRight x) {
        visitOperator(x);
    }

    public void visitUnsignedShiftRightAssignment(UnsignedShiftRightAssignment x) {
        visitOperator(x);
    }

    public void visitBreak(Break x) {
    }

    public void visitCase(Case x) {
    }

    public void visitCatch(Catch x) {
    }

    public void visitContinue(Continue x) {
    }

    public void visitDefault(Default x) {
    }

    public void visitDo(Do x) {
    }

    public void visitElse(Else x) {
    }

    public void visitEmptyStatement(EmptyStatement x) {
    }

    public void visitFinally(Finally x) {
    }

    public void visitFor(For x) {
    }

    public void visitEnhancedFor(EnhancedFor x) {
    }

    public void visitAssert(Assert x) {
    }

    public void visitIf(If x) {
    }

    public void visitLabeledStatement(LabeledStatement x) {
    }

    public void visitReturn(Return x) {
    }

    public void visitSwitch(Switch x) {
    }

    public void visitSynchronizedBlock(SynchronizedBlock x) {
    }

    public void visitThen(Then x) {
    }

    public void visitThrow(Throw x) {
    }

    public void visitTry(Try x) {
    }

    public void visitWhile(While x) {
    }

    public void visitArrayReference(ArrayReference x) {
    }

    public void visitArrayLengthReference(ArrayLengthReference x) {
    }

    public void visitFieldReference(FieldReference x) {
    }

    public void visitMetaClassReference(MetaClassReference x) {
    }

    public void visitMethodReference(MethodReference x) {
    }

    public void visitPackageReference(PackageReference x) {
    }

    public void visitSuperConstructorReference(SuperConstructorReference x) {
    }

    public void visitSuperReference(SuperReference x) {
    }

    public void visitThisConstructorReference(ThisConstructorReference x) {
    }

    public void visitThisReference(ThisReference x) {
    }

    public void visitTypeReference(TypeReference x) {
    }

    public void visitUncollatedReferenceQualifier(UncollatedReferenceQualifier x) {
    }

    public void visitVariableReference(VariableReference x) {
    }

    protected void visitModifier(Modifier x) {
    }

    protected void visitLiteral(Literal x) {
    }

    protected void visitOperator(Operator x) {
    }

    protected void visitVariableDeclaration(VariableDeclaration x) {
    }

    public void visitSingleLineComment(SingleLineComment x) {
        visitComment(x);
    }

    public void visitDocComment(DocComment x) {
        visitComment(x);
    }

    public void visitComment(Comment x) {
    }

    public void visitEnumConstructorReference(EnumConstructorReference x) {
    }

    public void visitEnumConstantDeclaration(EnumConstantDeclaration x) {
    }

    public void visitEnumConstantSpecification(EnumConstantSpecification x) {
    }

    public void visitEnumDeclaration(EnumDeclaration x) {
    }

    public void visitTypeArgument(TypeArgumentDeclaration x) {
    }

    public void visitTypeParameter(TypeParameterDeclaration x) {
    }
}
