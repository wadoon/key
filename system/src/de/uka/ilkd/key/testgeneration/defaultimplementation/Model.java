package de.uka.ilkd.key.testgeneration.defaultimplementation;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.testgeneration.model.IModel;

/**
 * Default implementation of the {@link IModel} interface
 * 
 * @author christopher
 */
public class Model
        implements IModel {

    private final LinkedList<IModelVariable> variables = new LinkedList<>();

    /**
     * Return a filtered subset of variables in this model. Filters can be left
     * out to return all variables.
     */
    @SafeVarargs
    @Override
    public final List<IModelVariable> getVariables(IModelFilter... filters) {

        LinkedList<IModelVariable> filteredVariables =
                new LinkedList<IModelVariable>();

        for (IModelVariable variable : variables) {

            if (satisfiesFilters(variable, filters)) {

                filteredVariables.add(variable);
            }
        }

        return filteredVariables;
    }

    @Override
    public Map<String, IModelVariable> getVariableNameMapping(
            IModelFilter... filters) {

        List<IModelVariable> filteredVariables = getFilteredVariables(filters);

        HashMap<String, IModelVariable> variableMapping = new HashMap<>();

        for (IModelVariable variable : filteredVariables) {

            variableMapping.put(variable.getName(), variable);
        }
        return null;
    }

    /**
     * Add a variable to the Model
     * 
     * @param variable
     */
    public void addVariable(IModelVariable variable) {

        variables.add(variable);
    }

    private List<IModelVariable> getFilteredVariables(IModelFilter[] filters) {

        if (filters.length == 0) {
            return variables;
        }

        LinkedList<IModelVariable> filteredVariables =
                new LinkedList<IModelVariable>();

        for (IModelVariable variable : variables) {

            if (satisfiesFilters(variable, filters)) {

                filteredVariables.add(variable);
            }
        }
        return filteredVariables;
    }

    private boolean satisfiesFilters(
            IModelVariable variable,
            IModelFilter[] filters) {

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
