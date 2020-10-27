package recoder.service;

import recoder.Service;
import recoder.abstraction.Package;
import recoder.abstraction.*;

import java.util.List;

public interface NameInfo extends Service {
    Package createPackage(String paramString);

    Package getPackage(String paramString);

    List<Package> getPackages();

    Type getType(String paramString);

    List<Type> getTypes();

    List<ClassType> getTypes(Package paramPackage);

    ClassType getClassType(String paramString);

    ArrayType getArrayType(Type paramType);

    ArrayType createArrayType(Type paramType);

    ArrayType createArrayType(Type paramType, int paramInt);

    List<ClassType> getClassTypes();

    ClassType getNullType();

    PrimitiveType getBooleanType();

    PrimitiveType getByteType();

    PrimitiveType getShortType();

    PrimitiveType getIntType();

    PrimitiveType getLongType();

    PrimitiveType getFloatType();

    PrimitiveType getDoubleType();

    PrimitiveType getCharType();

    ClassType getJavaLangObject();

    ClassType getJavaLangString();

    ClassType getJavaLangBoolean();

    ClassType getJavaLangByte();

    ClassType getJavaLangCharacter();

    ClassType getJavaLangShort();

    ClassType getJavaLangInteger();

    ClassType getJavaLangLong();

    ClassType getJavaLangFloat();

    ClassType getJavaLangDouble();

    ClassType getJavaLangClass();

    ClassType getJavaLangCloneable();

    ClassType getJavaIoSerializable();

    ClassType getJavaLangAnnotationAnnotation();

    ClassType getJavaLangEnum();

    Field getField(String paramString);

    List<Field> getFields();

    void register(ClassType paramClassType);

    void register(Field paramField);

    void unregisterClassType(String paramString);

    void unregisterField(String paramString);

    ProgramModelElement getUnknownElement();

    Type getUnknownType();

    ClassType getUnknownClassType();

    Package getUnknownPackage();

    Method getUnknownMethod();

    Constructor getUnknownConstructor();

    Variable getUnknownVariable();

    Field getUnknownField();

    AnnotationProperty getUnknownAnnotationProperty();
}
