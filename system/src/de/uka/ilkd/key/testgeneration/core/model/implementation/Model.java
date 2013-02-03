package de.uka.ilkd.key.testgeneration.core.model.implementation;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.testgeneration.core.model.IModel;
import de.uka.ilkd.key.testgeneration.core.model.IModelObject;
import de.uka.ilkd.key.testgeneration.core.parsers.PathconditionTools;

/**
 * Default implementation of the {@link IModel} interface
 * 
 * @author christopher
 */
public class Model implements IModel {

    /**
     * Indicates whether this instance will use buffering or not in order to
     * avoid nullpointerexceptions.
     */
    // private final boolean useBuffer;

    /**
     * Buffers variables which currently cannot be inserted due to broken
     * reference dependencies. Primarily, this will occur when the user tries to
     * insert a variable as a field into an instace which currently does'nt
     * exist. This can happens if this class is used in non-postorder
     * visitations of {@link Term} ASTs. Use mainly to allow safe visitations.
     */
    private final HashMap<ModelVariable, ModelVariable> buffer = new HashMap<ModelVariable, ModelVariable>();

    /**
     * The {@link ModelVariable} instances represented on this heap.
     */
    private final LinkedList<ModelVariable> variables = new LinkedList<ModelVariable>();

    /**
     * Adds a variable to the heap, causing it to point to a given object
     * instance. If the variable already exists on the heap, this method will
     * cause the variable to point to the new instance instead, unless the
     * variable is declared as <code>final</code>.
     * 
     * @param variable
     *            the variable to be added
     * @param instance
     *            the instance the variable will point to. Can be
     *            <code>null</code>.
     */
    public void add(ModelVariable variable, Object instance) {

        /*
         * TODO: This should throw an exception, not fail silently.
         */
        if (!ModelVariable.isValidValueType(instance)) {
            return;
        }

        ModelVariable localVariable = lookupVariable(variable);

        if (localVariable == null) {

            variable.setValue(instance);

            if(instance instanceof ModelInstance) {
                ((ModelInstance)instance).addReferee(variable);
            }
            
            variables.add(variable);
        } else {

            if(instance instanceof ModelInstance) {
                ((ModelInstance)instance).addReferee(localVariable);
            }
            
            variable.setValue(instance);
        }
    }

    /**
     * Links two {@link ModelVariable} instances, causing target to point to the
     * {@link ModelInstance} which other is pointing to.
     * 
     * @param target
     *            the target variable, i.e. the one the address of the instance
     *            is being bound to. Cannot be <code>null</code>
     * @param other
     *            the other variable, i.e. the one currently holding the address
     *            of the instance. Cannot be <code>null</code>
     */
    public void assignPointer(ModelVariable target, ModelVariable other) {

        if (!target.equals(other)) {
            target = lookupVariable(target);
            other = lookupVariable(other);

            if (other != null) {
                target.setValue(other.getValue());
            } else {
                target.setValue(null);
            }
        }
    }

    /**
     * Adds a new variable without violating uniqueness
     * 
     * @param variable
     *            the variable to add
     */
    private void addVariableNoDuplicates(ModelVariable variable) {

        if (!variables.contains(variable)) {
            variables.add(variable);
        }
    }

    /**
     * Places the variable target as a field of the {@link ModelInstance}
     * referred to by the variable other.
     * 
     * @param target
     *            the variable to insert as a field
     * @param other
     *            the variable pointing to the object instance we are inserting
     *            into
     */
    public void assignField(ModelVariable target, ModelVariable other) {

        if (!target.equals(other)) {
            target = lookupVariable(target);
            ModelVariable localOther = lookupVariable(other);
            
            /*
             * If the other currently does not exist in the Model, buffer it for
             * subsequent insertion.
             */
            if (other == null) {
                buffer.put(other, target);
                return;
            }

            ModelInstance instance = (ModelInstance) localOther.getValue();
            instance.addField(target);
            target.setParentModelInstance(instance);
        }
    }

    /**
     * Synchronize the buffer by going through each buffered element, and seeing
     * if it can be inserted into the Model. If the element could be inserted,
     * remove it from the buffer.
     */
    private void synchronizeBuffer() {

        if (!buffer.isEmpty()) {

            for (ModelVariable variable : buffer.keySet()) {

                ModelVariable localVariable = lookupVariable(variable);

                if (localVariable != null) {

                    ModelVariable target = buffer.get(variable);

                    assignField(target, localVariable);

                    buffer.remove(variable);
                }
            }
        }
    }

    /**
     * Retrieves the actual in-memory reference to a variable, as represented on
     * the heap.
     * 
     * @param variable
     *            the variable to lookup
     */
    private ModelVariable lookupVariable(ModelVariable variable) {

        int index = variables.indexOf(variable);
        return index >= 0 ? variables.get(index) : null;
    }

    /**
     * {@inheritDoc}
     */
    @SafeVarargs
    @Override
    public final List<IModelObject> getVariables(IModelFilter... filters) {

        LinkedList<IModelObject> filteredVariables = new LinkedList<IModelObject>();

        for (ModelVariable variable : variables) {

            if (satisfiesFilters(variable, filters)) {

                filteredVariables.add(variable);
            }
        }
        return filteredVariables;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Map<String, IModelObject> getVariableNameMapping(
            IModelFilter... filters) {

        List<IModelObject> filteredVariables = getFilteredVariables(filters);

        HashMap<String, IModelObject> variableMapping = new HashMap<String, IModelObject>();

        for (IModelObject variable : filteredVariables) {

            variableMapping.put(variable.getName(), variable);
        }
        return variableMapping;
    }

    /**
     * Returns the {@link ModelVariable} instance having a specific reference.
     * 
     * @param reference
     *            the reference
     * @return the found instance, null if no instance is found with the
     *         specified reference
     */
    public ModelVariable getVariableByReference(String reference) {

        for (ModelVariable variable : variables) {

            if (variable.getIdentifier().equals(reference)) {
                return variable;
            }
        }
        return null;
    }

    /**
     * Consumes the output of an SMT solver, connecting values to their
     * corresponding variables.
     * 
     * @param smtOutput
     */
    public void consumeSMTOutput(String smtOutput) {

        /*
         * Break the SMT output into individual variable declarations and
         * process them separately.
         */
        String[] definitions = smtOutput.trim().split("\\(define-fun");
        for (String definition : definitions) {

            if (!definition.isEmpty() && !definition.trim().startsWith("sat")) {

                definition = definition.trim();

                /*
                 * Extract the variable name
                 */
                String varName = definition.substring(0,
                        definition.lastIndexOf('_'));

                /*
                 * Extract the value
                 */
                String result = "";
                boolean negFlag = false;
                for (int i = definition.indexOf(' '); i < definition.length(); i++) {

                    char currentChar = definition.charAt(i);

                    if (!negFlag && currentChar == '-') {
                        negFlag = true;
                    }

                    if (Character.isDigit(currentChar)) {
                        result += currentChar;
                    }
                }

                Integer value = (negFlag) ? Integer.parseInt(result) * -1
                        : Integer.parseInt(result);
                ModelVariable variable = getVariableByReference(varName);
                if (variable != null) {
                    variable.setValue(value);
                }
            }
        }
    }
    
    /**
     * Determines if a given {@link ModelVariable} satisfied the conditions
     * postulated in a given set of {@link IModelFilter} instances.
     * 
     * @param variable
     *            the variable to check
     * @param filters
     *            the filters to check against
     * @return
     */
    private boolean satisfiesFilters(ModelVariable variable,
            IModelFilter[] filters) {

        for (IModelFilter filter : filters) {
            if (!filter.satisfies(variable)) {
                return false;
            }
        }
        return true;
    }

    private List<IModelObject> getFilteredVariables(IModelFilter[] filters) {

        LinkedList<IModelObject> filteredVariables = new LinkedList<IModelObject>();

        for (ModelVariable variable : variables) {

            if (satisfiesFilters(variable, filters)) {

                filteredVariables.add(variable);
            }
        }
        return filteredVariables;
    }

    /**
     * Filter objects according to name.
     * 
     * @author christopher
     */
    public static class NameFilter implements IModelFilter {

        private String name;

        public NameFilter(String name) {

            this.name = name;
        }

        @Override
        public boolean satisfies(IModelObject object) {

            return object.getName().equals(name);
        }
    }
}
