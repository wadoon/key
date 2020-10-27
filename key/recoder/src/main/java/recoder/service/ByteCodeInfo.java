package recoder.service;

import recoder.abstraction.*;
import recoder.bytecode.*;

public interface ByteCodeInfo extends ProgramModelInfo {
    void register(ClassFile paramClassFile);

    ClassFile getClassFile(ClassType paramClassType);

    MethodInfo getMethodInfo(Method paramMethod);

    ConstructorInfo getConstructorInfo(Constructor paramConstructor);

    FieldInfo getFieldInfo(Field paramField);

    Type getAnnotationType(AnnotationUseInfo paramAnnotationUseInfo);
}
