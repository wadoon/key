package de.tud.cs.se.ds.psec.compiler;

import java.util.HashMap;

import de.uka.ilkd.key.logic.op.IProgramVariable;

/**
 * Helper class to establish a mapping between program variables and their
 * indices. We use the <b>names</b> of the program variables since KeY will
 * do the disambiguation for us.
 *
 * @author Dominic Scheurer
 */
public class ProgVarHelper {
    private HashMap<String, Integer> progVarOffsetMap = new HashMap<>();
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
        String progVarName = progVar.toString();
        
        if (progVarOffsetMap.containsKey(progVarName)) {
            return progVarOffsetMap.get(progVarName);
        } else {
            // Offset 0 for "this" pointer, following ones for method
            // parameters, then for local variables.
            int offset = progVarOffsetMap.size() + (isStatic ? 0 : 1);
            progVarOffsetMap.put(progVarName, offset);

            return offset;
        }
    }

}
