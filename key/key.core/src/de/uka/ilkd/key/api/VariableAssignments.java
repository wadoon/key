package de.uka.ilkd.key.api;

import de.uka.ilkd.key.macros.scripts.meta.Type;

/**
 * Created by sarah on 4/21/17.
 */
public class VariableAssignments {
    //hashmaps mit variablen zuweisungen und pointer zu eltern hashmap
    private VariableAssignments parent;

    public VariableAssignments() {
    }

    public VariableAssignments(VariableAssignments parent) {
        this.parent = parent;
    }

    public Object getValue(String name) {
        return null;
    }

    public Type getType() {
        return null;
    }

    public void setType(Type type) {

    }

    public void setValue(String name) {

    }
}
