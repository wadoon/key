package recoder.abstraction;

import java.util.List;

public interface Method extends Member, ClassTypeContainer {
    List<Type> getSignature();

    List<ClassType> getExceptions();

    Type getReturnType();

    boolean isAbstract();

    boolean isNative();

    boolean isSynchronized();

    boolean isVarArgMethod();

    List<? extends TypeParameter> getTypeParameters();
}
