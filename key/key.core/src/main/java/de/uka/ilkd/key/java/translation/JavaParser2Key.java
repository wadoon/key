package de.uka.ilkd.key.java.translation;

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.key.*;
import com.github.javaparser.ast.key.sv.*;
import com.github.javaparser.ast.modules.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import com.github.javaparser.ast.visitor.GenericVisitor;
import de.uka.ilkd.key.java.ast.JavaProgramElement;
import de.uka.ilkd.key.java.ast.PackageSpecification;
import de.uka.ilkd.key.java.ast.ProgramElement;

import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (11/7/21)
 */
public class JavaParser2Key implements GenericVisitor<JavaProgramElement, Void> {
    private final Map<ProgramElement, Node> mapping;

    public JavaParser2Key(Map<ProgramElement, Node> mapping) {
        this.mapping = mapping;
    }

    @Override
    public JavaProgramElement visit(CompilationUnit n, Void arg) {
        return new de.uka.ilkd.key.java.ast.CompilationUnit(
                (PackageSpecification) n.getPackageDeclaration().map(it -> it.accept(this, arg)).orElse(null),
                arrayOf(n.getImports(), arg),
                arrayOf(n.getTypes(), arg)
        );
    }

    private <T> T[] arrayOf(NodeList<? extends Node> types, Void arg) {
        return (T[]) types.stream().map(it -> (T) it.accept(this, arg)).toArray();
    }

    @Override
    public JavaProgramElement visit(PackageDeclaration n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(TypeParameter n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(LineComment n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(BlockComment n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ClassOrInterfaceDeclaration n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(RecordDeclaration n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(CompactConstructorDeclaration n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(EnumDeclaration n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(EnumConstantDeclaration n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(AnnotationDeclaration n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(AnnotationMemberDeclaration n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(FieldDeclaration n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(VariableDeclarator n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ConstructorDeclaration n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(MethodDeclaration n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(Parameter n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(InitializerDeclaration n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(JavadocComment n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ClassOrInterfaceType n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(PrimitiveType n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ArrayType n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ArrayCreationLevel n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(IntersectionType n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(UnionType n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(VoidType n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(WildcardType n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(UnknownType n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ArrayAccessExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ArrayCreationExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ArrayInitializerExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(AssignExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(BinaryExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(CastExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ClassExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ConditionalExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(EnclosedExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(FieldAccessExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(InstanceOfExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(StringLiteralExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(IntegerLiteralExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(LongLiteralExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(CharLiteralExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(DoubleLiteralExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(BooleanLiteralExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(NullLiteralExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(MethodCallExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(NameExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ObjectCreationExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ThisExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(SuperExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(UnaryExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(VariableDeclarationExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(MarkerAnnotationExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(SingleMemberAnnotationExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(NormalAnnotationExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(MemberValuePair n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ExplicitConstructorInvocationStmt n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(LocalClassDeclarationStmt n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(LocalRecordDeclarationStmt n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(AssertStmt n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(BlockStmt n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(LabeledStmt n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(EmptyStmt n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ExpressionStmt n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(SwitchStmt n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(SwitchEntry n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(BreakStmt n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ReturnStmt n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(IfStmt n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(WhileStmt n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ContinueStmt n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(DoStmt n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ForEachStmt n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ForStmt n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ThrowStmt n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(SynchronizedStmt n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(TryStmt n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(CatchClause n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(LambdaExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(MethodReferenceExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(TypeExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(NodeList n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(Name n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(SimpleName n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ImportDeclaration n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ModuleDeclaration n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ModuleRequiresDirective n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ModuleExportsDirective n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ModuleProvidesDirective n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ModuleUsesDirective n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ModuleOpensDirective n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(UnparsableStmt n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(ReceiverParameter n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(VarType n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(Modifier n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(SwitchExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(YieldStmt n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(TextBlockLiteralExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(PatternExpr n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeYCcatchBreak n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeYCcatchContinue n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeYCcatchParameter n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeYCcatchReturn n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyCatchAllStatement n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyEscapeExpression n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyExecStatement n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyExecutionContext n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyLoopScopeBlock n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyMergePointStatement n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyMethodBodyStatement n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyMethodCallStatement n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyMethodSignature n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyRangeExpression n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyTransactionStatement n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyContextStatementBlock n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyExecCtxtSV n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyExpressionSV n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyJumpLabelSV n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyMetaConstructExpression n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyMetaConstruct n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyMetaConstructType n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyMethodSignatureSV n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyPassiveExpression n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyProgramVariableSV n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyStatementSV n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyTypeSV n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyCcatchSV n, Void arg) {
        return null;
    }

    @Override
    public JavaProgramElement visit(KeyExecutionContextSV n, Void arg) {
        return null;
    }
}
