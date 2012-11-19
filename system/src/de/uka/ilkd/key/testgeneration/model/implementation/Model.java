package de.uka.ilkd.key.testgeneration.model.implementation;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import com.sun.xml.internal.ws.org.objectweb.asm.MethodVisitor;

import de.uka.ilkd.key.testgeneration.model.IModel;
import de.uka.ilkd.key.testgeneration.model.IModelVariable;

/**
 * Default implementation of the {@link IModel} interface
 * 
 * @author christopher
 */
public class Model
        implements IModel {

    private final LinkedList<ModelVariable> variables = new LinkedList<ModelVariable>();

    /**
     * Return a filtered subset of variables in this model. Filters can be left out to return all
     * variables.
     */
    @SafeVarargs
    @Override
    public final List<IModelVariable> getVariables(IModelFilter... filters) {

        LinkedList<IModelVariable> filteredVariables = new LinkedList<IModelVariable>();

        for (IModelVariable variable : variables) {

            if (satisfiesFilters(variable, filters)) {

                filteredVariables.add(variable);
            }
        }

        return filteredVariables;
    }

    @Override
    public Map<String, IModelVariable> getVariableNameMapping(IModelFilter... filters) {

        List<IModelVariable> filteredVariables = getFilteredVariables(filters);

        HashMap<String, IModelVariable> variableMapping =
                new HashMap<String, IModelVariable>();

        for (IModelVariable variable : filteredVariables) {

            variableMapping.put(variable.getName(), variable);
        }
        return variableMapping;
    }

    public void add(ModelVariable variable) {

        /*
         * If the variable does not have a parent, it is a local variable, and we just insert it
         * as-is.
         */
        if (variable.getParent() == null) {
            if (!variables.contains(variable)) {
                variables.add(variable);
            }
        }

        /*
         * If the parent is not null, then this variable is either static, or part of a reference
         * field in the main class. In this case we search for a reference to the parent and insert
         * it as a childnode there.
         */
        else {
            for (ModelVariable modelVariable : variables) {

                /*
                 * Shortcircuit the insertion if the value has been succesfully inserted.
                 */
                if (insertIntoModel(variable, modelVariable)) {
                    return;
                }
            }
        }
    }

    /**
     * Recursively insert a {@link ModelVariable} into the {@link Model} as a child of its parent.
     * 
     * @param variable
     * @param target
     * @return
     */
    private boolean insertIntoModel(ModelVariable variable, ModelVariable target) {

        if (target.equals(variable.getParent())) {
            target.addChild(variable);
            return true;
        }
        else {
            for (ModelVariable child : target.getChildren()) {
                if(insertIntoModel(variable, child)) {
                    return true;
                }
            }
        }
        return false;
    }

    private List<IModelVariable> getFilteredVariables(IModelFilter[] filters) {

        LinkedList<IModelVariable> filteredVariables = new LinkedList<IModelVariable>();

        for (IModelVariable variable : variables) {

            if (satisfiesFilters(variable, filters)) {

                filteredVariables.add(variable);
            }
        }
        return filteredVariables;
    }

    private boolean satisfiesFilters(IModelVariable variable, IModelFilter[] filters) {

        for (IModelFilter filter : filters) {
            if (!filter.satisfies(variable)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Filter variables according to name.
     * 
     * @author christopher
     */
    public static class NameFilter
            implements IModelFilter {

        private String name;

        public NameFilter(String name) {

            this.name = name;
        }

        @Override
        public boolean satisfies(IModelVariable object) {

            return object.getName().equals(name);
        }
    }
}
