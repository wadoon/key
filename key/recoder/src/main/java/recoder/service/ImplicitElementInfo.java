package recoder.service;

import recoder.abstraction.ClassType;
import recoder.abstraction.DefaultConstructor;
import recoder.abstraction.ImplicitEnumMethod;
import recoder.java.declaration.EnumDeclaration;

import java.util.List;

public interface ImplicitElementInfo extends ProgramModelInfo {
    DefaultConstructor getDefaultConstructor(ClassType paramClassType);

    List<ImplicitEnumMethod> getImplicitEnumMethods(EnumDeclaration paramEnumDeclaration);
}
