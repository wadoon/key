package recoder.service;

import recoder.abstraction.Package;
import recoder.abstraction.*;
import recoder.java.Expression;
import recoder.java.ProgramElement;
import recoder.java.Reference;
import recoder.java.Statement;
import recoder.java.declaration.*;
import recoder.java.reference.*;
import recoder.java.statement.EmptyStatement;
import recoder.util.ProgressListener;

import java.util.List;

public interface SourceInfo extends ProgramModelInfo {
    Statement METHOD_EXIT = new EmptyStatement();

    ClassType getContainingClassType(ProgramElement paramProgramElement);

    Package getPackage(PackageReference paramPackageReference);

    Type getType(ProgramElement paramProgramElement);

    Type getType(TypeReference paramTypeReference);

    ClassType getType(TypeDeclaration paramTypeDeclaration);

    Type getType(VariableSpecification paramVariableSpecification);

    Type getType(String paramString, ProgramElement paramProgramElement);

    Type getType(Expression paramExpression);

    boolean isNarrowingTo(Expression paramExpression, PrimitiveType paramPrimitiveType);

    Variable getVariable(String paramString, ProgramElement paramProgramElement);

    Variable getVariable(VariableSpecification paramVariableSpecification);

    Variable getVariable(VariableReference paramVariableReference);

    Field getField(FieldReference paramFieldReference);

    List<FieldSpecification> getFields(TypeDeclaration paramTypeDeclaration);

    List<TypeDeclaration> getTypes(TypeDeclaration paramTypeDeclaration);

    Method getMethod(MethodDeclaration paramMethodDeclaration);

    List<Method> getMethods(TypeDeclaration paramTypeDeclaration);

    Method getMethod(MethodReference paramMethodReference);

    AnnotationProperty getAnnotationProperty(AnnotationPropertyReference paramAnnotationPropertyReference);

    List<Method> getMethods(MethodReference paramMethodReference);

    Constructor getConstructor(ConstructorDeclaration paramConstructorDeclaration);

    List<Constructor> getConstructors(TypeDeclaration paramTypeDeclaration);

    Constructor getConstructor(ConstructorReference paramConstructorReference);

    List<? extends Constructor> getConstructors(ConstructorReference paramConstructorReference);

    List<Type> makeSignature(List<Expression> paramList);

    Reference resolveURQ(UncollatedReferenceQualifier paramUncollatedReferenceQualifier);

    void register(ProgramElement paramProgramElement);

    TypeDeclaration getTypeDeclaration(ClassType paramClassType);

    MethodDeclaration getMethodDeclaration(Method paramMethod);

    ConstructorDeclaration getConstructorDeclaration(Constructor paramConstructor);

    VariableSpecification getVariableSpecification(Variable paramVariable);

    List<Statement> getSucceedingStatements(Statement paramStatement);

    void addProgressListener(ProgressListener paramProgressListener);

    void removeProgressListener(ProgressListener paramProgressListener);

    Type getAnnotationType(AnnotationUseSpecification paramAnnotationUseSpecification);
}
