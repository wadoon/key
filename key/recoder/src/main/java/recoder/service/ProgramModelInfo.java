package recoder.service;

import recoder.Service;
import recoder.abstraction.Package;
import recoder.abstraction.*;

import java.util.List;

public interface ProgramModelInfo extends Service {
    Type getType(ProgramModelElement paramProgramModelElement);

    Package getPackage(ProgramModelElement paramProgramModelElement);

    List<? extends ClassType> getTypes(ClassTypeContainer paramClassTypeContainer);

    List<ClassType> getAllTypes(ClassType paramClassType);

    ClassTypeContainer getClassTypeContainer(ClassType paramClassType);

    List<ClassType> getSupertypes(ClassType paramClassType);

    List<ClassType> getAllSupertypes(ClassType paramClassType);

    List<ClassType> getSubtypes(ClassType paramClassType);

    List<ClassType> getAllSubtypes(ClassType paramClassType);

    List<? extends Field> getFields(ClassType paramClassType);

    List<Field> getAllFields(ClassType paramClassType);

    List<? extends Constructor> getConstructors(ClassType paramClassType);

    List<Method> getMethods(ClassType paramClassType);

    List<Method> getAllMethods(ClassType paramClassType);

    ClassType getContainingClassType(Member paramMember);

    List<Type> getSignature(Method paramMethod);

    List<ClassType> getExceptions(Method paramMethod);

    Type getReturnType(Method paramMethod);

    PrimitiveType getPromotedType(PrimitiveType paramPrimitiveType1, PrimitiveType paramPrimitiveType2);

    boolean isWidening(PrimitiveType paramPrimitiveType1, PrimitiveType paramPrimitiveType2);

    boolean isWidening(ClassType paramClassType1, ClassType paramClassType2);

    boolean isWidening(ArrayType paramArrayType1, ArrayType paramArrayType2);

    boolean isWidening(Type paramType1, Type paramType2);

    boolean isSubtype(ClassType paramClassType1, ClassType paramClassType2);

    boolean isSupertype(ClassType paramClassType1, ClassType paramClassType2);

    boolean isVisibleFor(Member paramMember, ClassType paramClassType);

    boolean isCompatibleSignature(List<Type> paramList1, List<Type> paramList2);

    boolean isCompatibleSignature(List<Type> paramList1, List<Type> paramList2, boolean paramBoolean1, boolean paramBoolean2);

    void filterApplicableMethods(List<Method> paramList, String paramString, List<Type> paramList1, ClassType paramClassType);

    void filterMostSpecificMethods(List<Method> paramList);

    void filterMostSpecificMethodsPhase2(List<Method> paramList);

    void filterMostSpecificMethodsPhase3(List<Method> paramList);

    List<Method> getMethods(ClassType paramClassType1, String paramString, List<Type> paramList, List<? extends TypeArgument> paramList1, ClassType paramClassType2);

    List<Method> getMethods(ClassType paramClassType, String paramString, List<Type> paramList);

    List<Method> getMethods(ClassType paramClassType, String paramString, List<Type> paramList, List<? extends TypeArgument> paramList1);

    List<? extends Constructor> getConstructors(ClassType paramClassType, List<Type> paramList);

    ClassType getBoxedType(PrimitiveType paramPrimitiveType);

    PrimitiveType getUnboxedType(ClassType paramClassType);
}
