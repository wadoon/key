package de.tud.cs.se.ds.psec.compiler;

import java.util.HashMap;

import de.uka.ilkd.key.logic.op.IProgramVariable;

/**
 * Helper class to establish a mapping between program variables and their
 * indices.
 *
 * @author Dominic Scheurer
 */
public class ProgVarHelper {
    private HashMap<IProgramVariable, Integer> progVarOffsetMap = new HashMap<>();
    private boolean isStatic;

    /**
     * TODO
     * 
     * @param isStatic
     */
    public ProgVarHelper(boolean isStatic) {
        this.isStatic = isStatic;
    }

    /**
     * TODO
     *
     * @param progVar
     * @return
     */
    public int progVarNr(IProgramVariable progVar) {

        if (progVarOffsetMap.containsKey(progVar)) {
            return progVarOffsetMap.get(progVar);
        } else {
            // Offset 0 for "this" pointer, following ones for method
            // parameters, then for local variables.
            // XXX: Does this also work for variables with the same name
            // declared in different scopes?
            int offset = progVarOffsetMap.size() + (isStatic ? 0 : 1);
            progVarOffsetMap.put(progVar, offset);

            return offset;
        }
    }

}
