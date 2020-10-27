package recoder.java;

import recoder.abstraction.ClassType;

import java.util.List;

public interface TypeScope extends ScopeDefiningElement {
    List<? extends ClassType> getTypesInScope();

    ClassType getTypeInScope(String paramString);

    void addTypeToScope(ClassType paramClassType, String paramString);

    void removeTypeFromScope(String paramString);
}
