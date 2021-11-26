package org.key_project.java;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;

import static org.key_project.java.JavaSorts.*;

/**
 * @author Alexander Weigl
 * @version 1 (11/24/21)
 */
public class JavaOperators {
    private final Sort intSort, realSort;
    //region Java statements
    //Not covered LocalClassDeclarationStmt();
    //Not covered LocalRecordDeclarationStmt();

    //Problematic!
    public final Function thisConstructorInvocationStmt = createJavaStatement("ThisConstructorInvocation", JAVA_EXPR);
    public final Function superConstructorInvocationStmt = createJavaStatement("ThisConstructorInvocation", JAVA_EXPR);
    public final Function ForStmt;
    public final Function Sequential;
    public final Function SwitchStmt;
    public final Function ForEachStmt;
    public final Function ContinueStmt;
    public final Function ExpressionStmt;
    public final Function WhileStmt;
    public final Function ReturnStmt;
    public final Function EmptyStmt;
    public final Function UnparsableStmt;
    public final Function DoStmt;
    public final Function SynchronizedStmt;
    public final Function LabeledStmt;
    public final Function YieldStmt;
    public final Function IfStmt;
    public final Function BreakStmt;
    public final Function AssertStmt;
    public final Function ThrowStmt;
    public final Function TryStmt;
    public final Function TryStmtWithResources;
    //endregion

    // region Jml statements
    public final Function JmlSetStatement;
    public final Function JmlUnreachableStmt;
    public final Function JmlGhostStatements;
    public final Function JmlRefiningStmt;
    //endregion

    //region Expression
    public final Function ArrayAccessExpr;

    // Not covered ClassExpr= createJavaExpr(1);
    public final Function LambdaExpr;
    public final Function ConditionalExpr;
    //public final Function AnnotationExpr;
    //public final Function MarkerAnnotationExpr;
    //public final Function SingleMemberAnnotationExpr;
    //public final Function NormalAnnotationExpr;
    public final Function InstanceOfExpr;
    public final Function CastExpr;
    public final Function ThisExpr;

    //Problemtic
    public final Function SwitchExpr;
    public final Function NullLiteralExpr;
    public final Function BooleanLiteralExpr;
    public final Function LiteralStringValueExpr;
    public final Function TextBlockLiteralExpr;
    public final Function CharLiteralExpr;
    public final Function DoubleLiteralExpr;
    public final Function LongLiteralExpr;
    public final Function StringLiteralExpr;
    public final Function IntegerLiteralExpr;

    //PROBLEMATIC
    public final Function ObjectCreationExpr;
    public final Function SuperExpr;

    public final Function BinaryMultExpr;
    public final Function BinaryAddExpr;
    public final Function BinaryDivExpr;
    public final Function BinaryModExpr;
    public final Function BinaryXorExpr;
    public final Function BinaryAndExpr;
    public final Function BinaryOrExpr;

    public final Function LogicalOrExpr;
    public final Function LogicalAndExpr;


    public final Function PatternExpr;
    public final Function ArrayCreationExpr;
    public final Function MethodCallExpr;
    public final Function AssignExpr;
    public final Function NameExpr;
    public final Function MethodReferenceExpr;
    public final Function EnclosedExpr;
    public final Function VariableDeclarationExpr;
    public final Function UnaryExprLogicalNegation;
    public final Function UnaryExprBitwiseNegation;
    public final Function UnaryExprMinus;
    public final Function ArrayInitializerExpr;
    public final Function TypeExpr;
    public final Function FieldAccessExpr;
    public final Function EmptyExpr;
    public final Function CommaExpr;
    public final Function PostIncrement = createJavaExpr("PostInc", JAVA_EXPR);
    public final Function PreIncrement = createJavaExpr("PreInc", JAVA_EXPR);
    public final Function PostDecrement = createJavaExpr("PostDec", JAVA_EXPR);
    public final Function PreDecrement = createJavaExpr("PreDec", JAVA_EXPR);
    //endregion

    public final NamespaceSet nss;

    public final Function AssignLogialAndExpr = createJavaExpr("LAndAssign", JAVA_EXPR, JAVA_EXPR);
    public final Function AssignBinaryAndExpr = createJavaExpr("BAndAssign", JAVA_EXPR, JAVA_EXPR);
    public final Function AssignAddExpr = createJavaExpr("AddAssign", JAVA_EXPR, JAVA_EXPR);
    public final Function EqualsExpr = createJavaExpr("Equals", JAVA_EXPR, JAVA_EXPR);
    public final Function GTEExpr = createJavaExpr("GTE", JAVA_EXPR, JAVA_EXPR);
    public final Function AssignSubExpr = createJavaExpr("SubAssign", JAVA_EXPR, JAVA_EXPR);
    public final Function AssignDivExpr = createJavaExpr("DivAssign", JAVA_EXPR, JAVA_EXPR);
    public final Function GTExpr = createJavaExpr("GTE", JAVA_EXPR, JAVA_EXPR);
    public final Function LTEExpr = createJavaExpr("LTE", JAVA_EXPR, JAVA_EXPR);
    public final Function LTExpr = createJavaExpr("LT", JAVA_EXPR, JAVA_EXPR);
    public final Function NotEqualsExpr = createJavaExpr("NotEquals", JAVA_EXPR, JAVA_EXPR);
    public final Function ShiftLeftExpr = createJavaExpr("ShiftLeft", JAVA_EXPR, JAVA_EXPR);
    public final Function ShiftLeftAssignExpr = createJavaExpr("ShiftLeftAssign", JAVA_EXPR, JAVA_EXPR);
    public final Function ShiftRightAssignExpr = createJavaExpr("ShiftRightAssign", JAVA_EXPR, JAVA_EXPR);
    public final Function ShiftRightExpr = createJavaExpr("ShiftRight", JAVA_EXPR, JAVA_EXPR);
    public final Function MultiAssignExpr = createJavaExpr("MultiAssign", JAVA_EXPR, JAVA_EXPR);
    public final Function EmptyName = createJavaName("Empty");
    public Function UnsignedShiftRightExpr;
    public Function UnsignedShiftRightAssignExpr;

    private Function createJavaName(String empty) {
        return new Function(new Name("j" + empty), JAVA_NAME);
    }


    public JavaOperators(NamespaceSet nss) {
        this.nss = nss;
        registerSorts(nss);
        intSort = nss.sorts().lookup("int");
        realSort = nss.sorts().lookup("real");

        Sequential = createJavaStatement("Block", JAVA_STATEMENT, JAVA_STATEMENT);

        ForStmt = createJavaStatement("For", JAVA_EXPR, JAVA_EXPR, JAVA_EXPR, JAVA_STATEMENT);
        SwitchStmt = createJavaStatement("Switch", JAVA_EXPR, JAVA_EXPR, JAVA_STATEMENT, JAVA_STATEMENT);
        ForEachStmt = createJavaStatement("ForEach", JAVA_EXPR, JAVA_EXPR, JAVA_STATEMENT);
        ContinueStmt = createJavaStatement("Continue", JAVA_EXPR);
        ExpressionStmt = createJavaStatement("Expression", JAVA_EXPR);
        WhileStmt = createJavaStatement("While", JAVA_EXPR, JAVA_STATEMENT);
        ReturnStmt = createJavaStatement("Return", JAVA_EXPR);
        EmptyStmt = createJavaStatement("Empty");
        UnparsableStmt = createJavaStatement("Unparsable");
        DoStmt = createJavaStatement("Do", JAVA_EXPR, JAVA_STATEMENT);
        SynchronizedStmt = createJavaStatement("Synchronized", JAVA_EXPR);
        LabeledStmt = createJavaStatement("Labeled", JAVA_EXPR, JAVA_STATEMENT);
        YieldStmt = createJavaStatement("Yield", JAVA_EXPR);
        IfStmt = createJavaStatement("If", JAVA_EXPR, JAVA_STATEMENT, JAVA_STATEMENT);
        BreakStmt = createJavaStatement("Break", JAVA_EXPR);
        AssertStmt = createJavaStatement("Assert", JAVA_EXPR);
        ThrowStmt = createJavaStatement("Throw", JAVA_EXPR);
        TryStmt = createJavaStatement("Try", JAVA_STATEMENT, JAVA_CATCH, JAVA_STATEMENT);
        TryStmtWithResources = createJavaStatement("TryStmtWithResources",
                JAVA_STATEMENT, JAVA_STATEMENT, JAVA_CATCH, JAVA_STATEMENT);
        //endregion

        // region Jml statements
        JmlSetStatement = createJavaStatement("JmlSetStatement", JAVA_EXPR, JAVA_EXPR);
        JmlUnreachableStmt = createJavaStatement("JmlUnreachable");
        JmlGhostStatements = createJavaStatement("JmlGhostStatements", JAVA_EXPR);
        JmlRefiningStmt = createJavaStatement("JmlRefining", JAVA_EXPR);
        //endregion

        //region Expression
        EmptyExpr = createJavaExpr("Empty");
        CommaExpr = createJavaExpr("Comma", JAVA_EXPR, JAVA_EXPR);
        ArrayAccessExpr = createJavaExpr("ArrayAccess", JAVA_EXPR, JAVA_EXPR);
        LambdaExpr = createJavaExpr("Lambda", JAVA_EXPR, JAVA_EXPR);
        ConditionalExpr = createJavaExpr("Conditional", JAVA_EXPR, JAVA_EXPR, JAVA_EXPR);

        //AnnotationExpr = createJavaExpr("Annotation", );
        //MarkerAnnotationExpr = createJavaExpr("MarkerAnnotation", );
        //SingleMemberAnnotationExpr = createJavaExpr("SingleMemberAnnotation", );
        //NormalAnnotationExpr = createJavaExpr("NormalAnnotation", );

        InstanceOfExpr = createJavaExpr("InstanceOf", JAVA_EXPR, JAVA_TYPE);
        CastExpr = createJavaExpr("Cast", JAVA_TYPE, JAVA_EXPR);
        ThisExpr = createJavaExpr("This");

        //Problemtic
        SwitchExpr = createJavaExpr("Switch");
        NullLiteralExpr = createJavaExpr("NullLiteral");
        BooleanLiteralExpr = createJavaExpr("BooleanLiteral", Sort.FORMULA);
        LiteralStringValueExpr = createJavaExpr("LiteralStringValue", JAVA_STRING);
        TextBlockLiteralExpr = createJavaExpr("TextBlockLiteral", JAVA_STRING);
        CharLiteralExpr = createJavaExpr("CharLiteral");
        DoubleLiteralExpr = createJavaExpr("DoubleLiteral", realSort);
        LongLiteralExpr = createJavaExpr("LongLiteral", intSort);
        StringLiteralExpr = createJavaExpr("StringLiteral", JAVA_STRING);
        IntegerLiteralExpr = createJavaExpr("IntegerLiteral", intSort);

        //PROBLEMATIC
        ObjectCreationExpr = createJavaExpr("ObjectCreation", JAVA_TYPE, JAVA_EXPR);
        SuperExpr = createJavaExpr("Super");
        BinaryMultExpr = createJavaExpr("BinaryMult", JAVA_EXPR, JAVA_EXPR);
        BinaryAddExpr = createJavaExpr("BinaryAdd", JAVA_EXPR, JAVA_EXPR);
        BinaryDivExpr = createJavaExpr("BinaryDiv", JAVA_EXPR, JAVA_EXPR);
        BinaryModExpr = createJavaExpr("BinaryMod", JAVA_EXPR, JAVA_EXPR);
        BinaryXorExpr = createJavaExpr("BinaryXor", JAVA_EXPR, JAVA_EXPR);
        BinaryAndExpr = createJavaExpr("BinaryAnd", JAVA_EXPR, JAVA_EXPR);
        BinaryOrExpr = createJavaExpr("BinaryOr", JAVA_EXPR, JAVA_EXPR);
        LogicalOrExpr = createJavaExpr("LogicalOr", JAVA_EXPR, JAVA_EXPR);
        LogicalAndExpr = createJavaExpr("LogicalAnd", JAVA_EXPR, JAVA_EXPR);

        PatternExpr = createJavaExpr("Pattern", JAVA_EXPR, JAVA_TYPE, JAVA_EXPR);
        ArrayCreationExpr = createJavaExpr("ArrayCreation", JAVA_TYPE, JAVA_EXPR);
        MethodCallExpr = createJavaExpr("MethodCall", JAVA_EXPR, JAVA_EXPR /*args*/);
        AssignExpr = createJavaExpr("Assign", JAVA_EXPR, JAVA_EXPR);
        NameExpr = createJavaExpr("Name", JAVA_EXPR);
        MethodReferenceExpr = createJavaExpr("MethodReference", JAVA_TYPE, JAVA_EXPR);
        EnclosedExpr = createJavaExpr("Enclosed", JAVA_EXPR);
        VariableDeclarationExpr = createJavaExpr("VariableDeclaration", JAVA_TYPE, JAVA_NAME, JAVA_EXPR);
        UnaryExprLogicalNegation = createJavaExpr("UnaryExprLogicalNegation", JAVA_EXPR);
        UnaryExprBitwiseNegation = createJavaExpr("UnaryExprBitwiseNegation", JAVA_EXPR);
        UnaryExprMinus = createJavaExpr("UnaryExprMinus", JAVA_EXPR);
        ArrayInitializerExpr = createJavaExpr("ArrayInitializer");
        TypeExpr = createJavaType("Type", JAVA_NAME);
        FieldAccessExpr = createJavaExpr("FieldAccess", JAVA_EXPR, JAVA_EXPR);
    }

    private Function createJavaType(String name, Sort... expected) {
        return new Function(new Name("j" + name), JAVA_TYPE, expected);
    }

    private Function createJavaStatement(String name, Sort... expected) {
        return new Function(new Name("js" + name), JAVA_STATEMENT, expected);
    }

    private Function createJavaExpr(String name, Sort... expected) {
        return new Function(new Name("je" + name), JAVA_EXPR, expected);
    }

    private void registerSorts(NamespaceSet nss) {
        nss.sorts().add(JAVA_STATEMENT);
        nss.sorts().add(JAVA_EXPR);
        nss.sorts().add(JAVA_CATCH);
        nss.sorts().add(JAVA_CASE);
        nss.sorts().add(JAVA_STRING);
        nss.sorts().add(JAVA_TYPE);
    }
}