package recoder.abstraction;

import java.util.List;

public interface ClassType extends Type, Member, ClassTypeContainer {
    boolean isInterface();

    boolean isOrdinaryInterface();

    boolean isAnnotationType();

    boolean isEnumType();

    boolean isOrdinaryClass();

    boolean isAbstract();

    List<ClassType> getSupertypes();

    List<ClassType> getAllSupertypes();

    List<? extends Field> getFields();

    List<Field> getAllFields();

    List<Method> getMethods();

    List<Method> getAllMethods();

    List<? extends Constructor> getConstructors();

    List<ClassType> getAllTypes();

    List<? extends TypeParameter> getTypeParameters();
}
