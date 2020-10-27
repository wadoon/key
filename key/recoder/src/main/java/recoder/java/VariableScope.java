package recoder.java;

import recoder.java.declaration.VariableSpecification;

import java.util.List;

public interface VariableScope extends ScopeDefiningElement {
    List<? extends VariableSpecification> getVariablesInScope();

    VariableSpecification getVariableInScope(String paramString);

    void addVariableToScope(VariableSpecification paramVariableSpecification);

    void removeVariableFromScope(String paramString);
}
