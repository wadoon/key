package de.tud.cs.se.ds.psec.compiler;

import java.util.HashMap;

import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.logic.op.IProgramVariable;

/**
 * Helper class to establish a mapping between program variables and their
 * indices. We use the <b>names</b> of the program variables since KeY will do
 * the disambiguation for us.
 *
 * @author Dominic Scheurer
 */
public class ProgVarHelper {
    private HashMap<String, Integer> progVarOffsetMap = new HashMap<>();
    private boolean isStatic;

    /**
     * Constructs a new {@link ProgVarHelper}. The helper has to know whether
     * the method of interest is static, because then there is no additional
     * "this" local variable.
     * 
     * @param isStatic
     *            true iff the method using this {@link ProgVarHelper} is
     *            static.
     * @param methodParameters
     *            The method parameters, for choosing the right indeces
     */
    public ProgVarHelper(boolean isStatic,
            Iterable<ParameterDeclaration> methodParameters) {
        this.isStatic = isStatic;

        for (ParameterDeclaration param : methodParameters) {
            progVarOffsetMap.put(param.getVariables().get(0).toString(),
                    progVarOffsetMap.size() + (isStatic ? 0 : 1));
        }
    }

    /**
     * Returns the index for the given {@link IProgramVariable}. Works such that
     * if the method has not been called for the {@link IProgramVariable} yet,
     * the next "free" number is returned and the number is cached for the name
     * of the {@link IProgramVariable}; otherwise, the cached number is
     * returned.
     *
     * @param progVar
     *            The {@link IProgramVariable} to obtain an index for.
     * @return The local variable index for the given {@link IProgramVariable}.
     */
    public int progVarNr(IProgramVariable progVar) {
        String progVarName = progVar.toString();

        if (progVarOffsetMap.containsKey(progVarName)) {
            return progVarOffsetMap.get(progVarName);
        }
        else {
            // Offset 0 for "this" pointer, following ones for method
            // parameters, then for local variables.
            int offset = progVarOffsetMap.size() + (isStatic ? 0 : 1);
            progVarOffsetMap.put(progVarName, offset);

            return offset;
        }
    }
    
    public static int test(int i) {
        boolean x;
        int x_1;
        int x_2 = i;
        int x_3 = i+1;
        i = x_3;
        x_1 = x_2;
        x = x_1 > 0;
        
        while (x) {
            i = i - 2;
            int x_5 = i;
            int x_6 = i + 1;
            i = x_6;
            int x_4 = x_5;
            x = x_4 > 0;
        }

        return i;
    }

}
