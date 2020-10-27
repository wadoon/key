package recoder;

import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.*;
import recoder.java.expression.ArrayInitializer;
import recoder.java.expression.ParenthesizedExpression;
import recoder.java.expression.literal.*;
import recoder.java.expression.operator.*;
import recoder.java.reference.*;
import recoder.java.statement.*;
import recoder.list.generic.ASTList;

import java.io.IOException;
import java.io.Reader;
import java.io.Writer;
import java.util.List;

public interface ProgramFactory extends Service {
    CompilationUnit parseCompilationUnit(Reader paramReader) throws IOException, ParserException;

    TypeDeclaration parseTypeDeclaration(Reader paramReader) throws IOException, ParserException;

    FieldDeclaration parseFieldDeclaration(Reader paramReader) throws IOException, ParserException;

    MethodDeclaration parseMethodDeclaration(Reader paramReader) throws IOException, ParserException;

    MemberDeclaration parseMemberDeclaration(Reader paramReader) throws IOException, ParserException;

    ParameterDeclaration parseParameterDeclaration(Reader paramReader) throws IOException, ParserException;

    ConstructorDeclaration parseConstructorDeclaration(Reader paramReader) throws IOException, ParserException;

    TypeReference parseTypeReference(Reader paramReader) throws IOException, ParserException;

    Expression parseExpression(Reader paramReader) throws IOException, ParserException;

    ASTList<Statement> parseStatements(Reader paramReader) throws IOException, ParserException;

    StatementBlock parseStatementBlock(Reader paramReader) throws IOException, ParserException;

    CompilationUnit parseCompilationUnit(String paramString) throws ParserException;

    List<CompilationUnit> parseCompilationUnits(String[] paramArrayOfString) throws ParserException;

    TypeDeclaration parseTypeDeclaration(String paramString) throws ParserException;

    MemberDeclaration parseMemberDeclaration(String paramString) throws ParserException;

    FieldDeclaration parseFieldDeclaration(String paramString) throws ParserException;

    MethodDeclaration parseMethodDeclaration(String paramString) throws ParserException;

    ParameterDeclaration parseParameterDeclaration(String paramString) throws ParserException;

    ConstructorDeclaration parseConstructorDeclaration(String paramString) throws ParserException;

    TypeReference parseTypeReference(String paramString) throws ParserException;

    Expression parseExpression(String paramString) throws ParserException;

    ASTList<Statement> parseStatements(String paramString) throws ParserException;

    PrettyPrinter getPrettyPrinter(Writer paramWriter);

    Comment createComment();

    Comment createComment(String paramString);

    Comment createComment(String paramString, boolean paramBoolean);

    CompilationUnit createCompilationUnit();

    CompilationUnit createCompilationUnit(PackageSpecification paramPackageSpecification, ASTList<Import> paramASTList, ASTList<TypeDeclaration> paramASTList1);

    DocComment createDocComment();

    DocComment createDocComment(String paramString);

    Identifier createIdentifier();

    Identifier createIdentifier(String paramString);

    Import createImport();

    Import createImport(TypeReference paramTypeReference, boolean paramBoolean);

    Import createImport(PackageReference paramPackageReference);

    Import createStaticImport(TypeReference paramTypeReference);

    Import createStaticImport(TypeReference paramTypeReference, Identifier paramIdentifier);

    PackageSpecification createPackageSpecification();

    PackageSpecification createPackageSpecification(PackageReference paramPackageReference);

    SingleLineComment createSingleLineComment();

    SingleLineComment createSingleLineComment(String paramString);

    TypeReference createTypeReference();

    TypeReference createTypeReference(Identifier paramIdentifier);

    TypeReference createTypeReference(ReferencePrefix paramReferencePrefix, Identifier paramIdentifier);

    TypeReference createTypeReference(Identifier paramIdentifier, int paramInt);

    PackageReference createPackageReference();

    PackageReference createPackageReference(Identifier paramIdentifier);

    PackageReference createPackageReference(PackageReference paramPackageReference, Identifier paramIdentifier);

    UncollatedReferenceQualifier createUncollatedReferenceQualifier();

    UncollatedReferenceQualifier createUncollatedReferenceQualifier(Identifier paramIdentifier);

    UncollatedReferenceQualifier createUncollatedReferenceQualifier(ReferencePrefix paramReferencePrefix, Identifier paramIdentifier);

    ClassDeclaration createClassDeclaration();

    ClassDeclaration createClassDeclaration(ASTList<DeclarationSpecifier> paramASTList, Identifier paramIdentifier, Extends paramExtends, Implements paramImplements, ASTList<MemberDeclaration> paramASTList1);

    ClassDeclaration createClassDeclaration(ASTList<MemberDeclaration> paramASTList);

    ClassInitializer createClassInitializer();

    ClassInitializer createClassInitializer(StatementBlock paramStatementBlock);

    ClassInitializer createClassInitializer(Static paramStatic, StatementBlock paramStatementBlock);

    ConstructorDeclaration createConstructorDeclaration();

    ConstructorDeclaration createConstructorDeclaration(VisibilityModifier paramVisibilityModifier, Identifier paramIdentifier, ASTList<ParameterDeclaration> paramASTList, Throws paramThrows, StatementBlock paramStatementBlock);

    Throws createThrows();

    Throws createThrows(TypeReference paramTypeReference);

    Throws createThrows(ASTList<TypeReference> paramASTList);

    FieldDeclaration createFieldDeclaration();

    FieldDeclaration createFieldDeclaration(TypeReference paramTypeReference, Identifier paramIdentifier);

    FieldDeclaration createFieldDeclaration(ASTList<DeclarationSpecifier> paramASTList, TypeReference paramTypeReference, Identifier paramIdentifier, Expression paramExpression);

    FieldDeclaration createFieldDeclaration(ASTList<DeclarationSpecifier> paramASTList, TypeReference paramTypeReference, ASTList<FieldSpecification> paramASTList1);

    Extends createExtends();

    Extends createExtends(TypeReference paramTypeReference);

    Extends createExtends(ASTList<TypeReference> paramASTList);

    Implements createImplements();

    Implements createImplements(TypeReference paramTypeReference);

    Implements createImplements(ASTList<TypeReference> paramASTList);

    InterfaceDeclaration createInterfaceDeclaration();

    InterfaceDeclaration createInterfaceDeclaration(ASTList<DeclarationSpecifier> paramASTList, Identifier paramIdentifier, Extends paramExtends, ASTList<MemberDeclaration> paramASTList1);

    AnnotationDeclaration createAnnotationDeclaration();

    AnnotationDeclaration createAnnotationDeclaration(ASTList<DeclarationSpecifier> paramASTList, Identifier paramIdentifier, ASTList<MemberDeclaration> paramASTList1);

    LocalVariableDeclaration createLocalVariableDeclaration();

    LocalVariableDeclaration createLocalVariableDeclaration(TypeReference paramTypeReference, Identifier paramIdentifier);

    LocalVariableDeclaration createLocalVariableDeclaration(ASTList<DeclarationSpecifier> paramASTList, TypeReference paramTypeReference, ASTList<VariableSpecification> paramASTList1);

    LocalVariableDeclaration createLocalVariableDeclaration(ASTList<DeclarationSpecifier> paramASTList, TypeReference paramTypeReference, Identifier paramIdentifier, Expression paramExpression);

    MethodDeclaration createMethodDeclaration();

    MethodDeclaration createMethodDeclaration(ASTList<DeclarationSpecifier> paramASTList, TypeReference paramTypeReference, Identifier paramIdentifier, ASTList<ParameterDeclaration> paramASTList1, Throws paramThrows);

    MethodDeclaration createMethodDeclaration(ASTList<DeclarationSpecifier> paramASTList, TypeReference paramTypeReference, Identifier paramIdentifier, ASTList<ParameterDeclaration> paramASTList1, Throws paramThrows, StatementBlock paramStatementBlock);

    AnnotationPropertyDeclaration createAnnotationPropertyDeclaration(ASTList<DeclarationSpecifier> paramASTList, TypeReference paramTypeReference, Identifier paramIdentifier, Expression paramExpression);

    ParameterDeclaration createParameterDeclaration();

    ParameterDeclaration createParameterDeclaration(TypeReference paramTypeReference, Identifier paramIdentifier);

    ParameterDeclaration createParameterDeclaration(ASTList<DeclarationSpecifier> paramASTList, TypeReference paramTypeReference, Identifier paramIdentifier);

    VariableSpecification createVariableSpecification();

    VariableSpecification createVariableSpecification(Identifier paramIdentifier);

    VariableSpecification createVariableSpecification(Identifier paramIdentifier, Expression paramExpression);

    VariableSpecification createVariableSpecification(Identifier paramIdentifier, int paramInt, Expression paramExpression);

    FieldSpecification createFieldSpecification();

    FieldSpecification createFieldSpecification(Identifier paramIdentifier);

    FieldSpecification createFieldSpecification(Identifier paramIdentifier, Expression paramExpression);

    FieldSpecification createFieldSpecification(Identifier paramIdentifier, int paramInt, Expression paramExpression);

    ArrayInitializer createArrayInitializer();

    ArrayInitializer createArrayInitializer(ASTList<Expression> paramASTList);

    ParenthesizedExpression createParenthesizedExpression();

    ParenthesizedExpression createParenthesizedExpression(Expression paramExpression);

    BooleanLiteral createBooleanLiteral();

    BooleanLiteral createBooleanLiteral(boolean paramBoolean);

    CharLiteral createCharLiteral();

    CharLiteral createCharLiteral(char paramChar);

    CharLiteral createCharLiteral(String paramString);

    DoubleLiteral createDoubleLiteral();

    DoubleLiteral createDoubleLiteral(double paramDouble);

    DoubleLiteral createDoubleLiteral(String paramString);

    FloatLiteral createFloatLiteral();

    FloatLiteral createFloatLiteral(float paramFloat);

    FloatLiteral createFloatLiteral(String paramString);

    IntLiteral createIntLiteral();

    IntLiteral createIntLiteral(int paramInt);

    IntLiteral createIntLiteral(String paramString);

    LongLiteral createLongLiteral();

    LongLiteral createLongLiteral(long paramLong);

    LongLiteral createLongLiteral(String paramString);

    NullLiteral createNullLiteral();

    StringLiteral createStringLiteral();

    StringLiteral createStringLiteral(String paramString);

    ArrayReference createArrayReference();

    ArrayReference createArrayReference(ReferencePrefix paramReferencePrefix, ASTList<Expression> paramASTList);

    FieldReference createFieldReference();

    FieldReference createFieldReference(Identifier paramIdentifier);

    FieldReference createFieldReference(ReferencePrefix paramReferencePrefix, Identifier paramIdentifier);

    MetaClassReference createMetaClassReference();

    MetaClassReference createMetaClassReference(TypeReference paramTypeReference);

    MethodReference createMethodReference();

    MethodReference createMethodReference(Identifier paramIdentifier);

    MethodReference createMethodReference(ReferencePrefix paramReferencePrefix, Identifier paramIdentifier);

    MethodReference createMethodReference(Identifier paramIdentifier, ASTList<Expression> paramASTList);

    MethodReference createMethodReference(ReferencePrefix paramReferencePrefix, Identifier paramIdentifier, ASTList<Expression> paramASTList);

    MethodReference createMethodReference(ReferencePrefix paramReferencePrefix, Identifier paramIdentifier, ASTList<Expression> paramASTList, ASTList<TypeArgumentDeclaration> paramASTList1);

    AnnotationPropertyReference createAnnotationPropertyReference(String paramString);

    AnnotationPropertyReference createAnnotationPropertyReference(Identifier paramIdentifier);

    SuperConstructorReference createSuperConstructorReference();

    SuperConstructorReference createSuperConstructorReference(ASTList<Expression> paramASTList);

    SuperConstructorReference createSuperConstructorReference(ReferencePrefix paramReferencePrefix, ASTList<Expression> paramASTList);

    SuperReference createSuperReference();

    SuperReference createSuperReference(ReferencePrefix paramReferencePrefix);

    ThisConstructorReference createThisConstructorReference();

    ThisConstructorReference createThisConstructorReference(ASTList<Expression> paramASTList);

    ThisReference createThisReference();

    ThisReference createThisReference(TypeReference paramTypeReference);

    VariableReference createVariableReference();

    VariableReference createVariableReference(Identifier paramIdentifier);

    ArrayLengthReference createArrayLengthReference();

    ArrayLengthReference createArrayLengthReference(ReferencePrefix paramReferencePrefix);

    BinaryAnd createBinaryAnd();

    BinaryAnd createBinaryAnd(Expression paramExpression1, Expression paramExpression2);

    BinaryAndAssignment createBinaryAndAssignment();

    BinaryAndAssignment createBinaryAndAssignment(Expression paramExpression1, Expression paramExpression2);

    BinaryNot createBinaryNot();

    BinaryNot createBinaryNot(Expression paramExpression);

    BinaryOr createBinaryOr();

    BinaryOr createBinaryOr(Expression paramExpression1, Expression paramExpression2);

    BinaryOrAssignment createBinaryOrAssignment();

    BinaryOrAssignment createBinaryOrAssignment(Expression paramExpression1, Expression paramExpression2);

    BinaryXOr createBinaryXOr();

    BinaryXOr createBinaryXOr(Expression paramExpression1, Expression paramExpression2);

    BinaryXOrAssignment createBinaryXOrAssignment();

    BinaryXOrAssignment createBinaryXOrAssignment(Expression paramExpression1, Expression paramExpression2);

    Conditional createConditional();

    Conditional createConditional(Expression paramExpression1, Expression paramExpression2, Expression paramExpression3);

    CopyAssignment createCopyAssignment();

    CopyAssignment createCopyAssignment(Expression paramExpression1, Expression paramExpression2);

    Divide createDivide();

    Divide createDivide(Expression paramExpression1, Expression paramExpression2);

    DivideAssignment createDivideAssignment();

    DivideAssignment createDivideAssignment(Expression paramExpression1, Expression paramExpression2);

    Equals createEquals();

    Equals createEquals(Expression paramExpression1, Expression paramExpression2);

    GreaterOrEquals createGreaterOrEquals();

    GreaterOrEquals createGreaterOrEquals(Expression paramExpression1, Expression paramExpression2);

    GreaterThan createGreaterThan();

    GreaterThan createGreaterThan(Expression paramExpression1, Expression paramExpression2);

    Instanceof createInstanceof();

    Instanceof createInstanceof(Expression paramExpression, TypeReference paramTypeReference);

    LessOrEquals createLessOrEquals();

    LessOrEquals createLessOrEquals(Expression paramExpression1, Expression paramExpression2);

    LessThan createLessThan();

    LessThan createLessThan(Expression paramExpression1, Expression paramExpression2);

    LogicalAnd createLogicalAnd();

    LogicalAnd createLogicalAnd(Expression paramExpression1, Expression paramExpression2);

    LogicalNot createLogicalNot();

    LogicalNot createLogicalNot(Expression paramExpression);

    LogicalOr createLogicalOr();

    LogicalOr createLogicalOr(Expression paramExpression1, Expression paramExpression2);

    Minus createMinus();

    Minus createMinus(Expression paramExpression1, Expression paramExpression2);

    MinusAssignment createMinusAssignment();

    MinusAssignment createMinusAssignment(Expression paramExpression1, Expression paramExpression2);

    Modulo createModulo();

    Modulo createModulo(Expression paramExpression1, Expression paramExpression2);

    ModuloAssignment createModuloAssignment();

    ModuloAssignment createModuloAssignment(Expression paramExpression1, Expression paramExpression2);

    Negative createNegative();

    Negative createNegative(Expression paramExpression);

    New createNew();

    New createNew(ReferencePrefix paramReferencePrefix, TypeReference paramTypeReference, ASTList<Expression> paramASTList);

    New createNew(ReferencePrefix paramReferencePrefix, TypeReference paramTypeReference, ASTList<Expression> paramASTList, ClassDeclaration paramClassDeclaration);

    NewArray createNewArray();

    NewArray createNewArray(TypeReference paramTypeReference, ASTList<Expression> paramASTList);

    NewArray createNewArray(TypeReference paramTypeReference, int paramInt, ArrayInitializer paramArrayInitializer);

    NotEquals createNotEquals();

    NotEquals createNotEquals(Expression paramExpression1, Expression paramExpression2);

    Plus createPlus();

    Plus createPlus(Expression paramExpression1, Expression paramExpression2);

    PlusAssignment createPlusAssignment();

    PlusAssignment createPlusAssignment(Expression paramExpression1, Expression paramExpression2);

    Positive createPositive();

    Positive createPositive(Expression paramExpression);

    PostDecrement createPostDecrement();

    PostDecrement createPostDecrement(Expression paramExpression);

    PostIncrement createPostIncrement();

    PostIncrement createPostIncrement(Expression paramExpression);

    PreDecrement createPreDecrement();

    PreDecrement createPreDecrement(Expression paramExpression);

    PreIncrement createPreIncrement();

    PreIncrement createPreIncrement(Expression paramExpression);

    ShiftLeft createShiftLeft();

    ShiftLeft createShiftLeft(Expression paramExpression1, Expression paramExpression2);

    ShiftLeftAssignment createShiftLeftAssignment();

    ShiftLeftAssignment createShiftLeftAssignment(Expression paramExpression1, Expression paramExpression2);

    ShiftRight createShiftRight();

    ShiftRight createShiftRight(Expression paramExpression1, Expression paramExpression2);

    ShiftRightAssignment createShiftRightAssignment();

    ShiftRightAssignment createShiftRightAssignment(Expression paramExpression1, Expression paramExpression2);

    Times createTimes();

    Times createTimes(Expression paramExpression1, Expression paramExpression2);

    TimesAssignment createTimesAssignment();

    TimesAssignment createTimesAssignment(Expression paramExpression1, Expression paramExpression2);

    TypeCast createTypeCast();

    TypeCast createTypeCast(Expression paramExpression, TypeReference paramTypeReference);

    UnsignedShiftRight createUnsignedShiftRight();

    UnsignedShiftRight createUnsignedShiftRight(Expression paramExpression1, Expression paramExpression2);

    UnsignedShiftRightAssignment createUnsignedShiftRightAssignment();

    UnsignedShiftRightAssignment createUnsignedShiftRightAssignment(Expression paramExpression1, Expression paramExpression2);

    Abstract createAbstract();

    Final createFinal();

    Native createNative();

    Private createPrivate();

    Protected createProtected();

    Public createPublic();

    Static createStatic();

    Synchronized createSynchronized();

    Transient createTransient();

    StrictFp createStrictFp();

    Volatile createVolatile();

    AnnotationUseSpecification createAnnotationUseSpecification();

    Break createBreak();

    Break createBreak(Identifier paramIdentifier);

    Case createCase();

    Case createCase(Expression paramExpression);

    Case createCase(Expression paramExpression, ASTList<Statement> paramASTList);

    Catch createCatch();

    Catch createCatch(ParameterDeclaration paramParameterDeclaration, StatementBlock paramStatementBlock);

    Continue createContinue();

    Continue createContinue(Identifier paramIdentifier);

    Default createDefault();

    Default createDefault(ASTList<Statement> paramASTList);

    Do createDo();

    Do createDo(Expression paramExpression);

    Do createDo(Expression paramExpression, Statement paramStatement);

    Else createElse();

    Else createElse(Statement paramStatement);

    EmptyStatement createEmptyStatement();

    Finally createFinally();

    Finally createFinally(StatementBlock paramStatementBlock);

    For createFor();

    For createFor(ASTList<LoopInitializer> paramASTList, Expression paramExpression, ASTList<Expression> paramASTList1, Statement paramStatement);

    EnhancedFor createEnhancedFor();

    Assert createAssert();

    Assert createAssert(Expression paramExpression);

    Assert createAssert(Expression paramExpression1, Expression paramExpression2);

    If createIf();

    If createIf(Expression paramExpression, Statement paramStatement);

    If createIf(Expression paramExpression, Then paramThen);

    If createIf(Expression paramExpression, Then paramThen, Else paramElse);

    If createIf(Expression paramExpression, Statement paramStatement1, Statement paramStatement2);

    LabeledStatement createLabeledStatement();

    LabeledStatement createLabeledStatement(Identifier paramIdentifier);

    LabeledStatement createLabeledStatement(Identifier paramIdentifier, Statement paramStatement);

    Return createReturn();

    Return createReturn(Expression paramExpression);

    StatementBlock createStatementBlock();

    StatementBlock createStatementBlock(ASTList<Statement> paramASTList);

    Switch createSwitch();

    Switch createSwitch(Expression paramExpression);

    Switch createSwitch(Expression paramExpression, ASTList<Branch> paramASTList);

    SynchronizedBlock createSynchronizedBlock();

    SynchronizedBlock createSynchronizedBlock(StatementBlock paramStatementBlock);

    SynchronizedBlock createSynchronizedBlock(Expression paramExpression, StatementBlock paramStatementBlock);

    Then createThen();

    Then createThen(Statement paramStatement);

    Throw createThrow();

    Throw createThrow(Expression paramExpression);

    Try createTry();

    Try createTry(StatementBlock paramStatementBlock);

    Try createTry(StatementBlock paramStatementBlock, ASTList<Branch> paramASTList);

    While createWhile();

    While createWhile(Expression paramExpression);

    While createWhile(Expression paramExpression, Statement paramStatement);
}
