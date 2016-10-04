package de.tud.cs.se.ds.psec.parser.ast;

import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * A container class for inputs that are relevant for assessing the
 * applicability of a translation rule.
 *
 * @author Dominic Scheurer
 */
public class ApplicabilityCheckInput {

    private int numChildren;
    private SVInstantiations schemaVarInstantiations;

    /**
     * @param numChildren
     *            The number of children in the symbolic execution taclet AST.
     * @param schemaVarInstantiations
     *            The instantiations for schema variables in the symbolic
     *            execution {@link Taclet} to be translated.
     */
    public ApplicabilityCheckInput(int numChildren,
            SVInstantiations schemaVarInstantiations) {
        this.numChildren = numChildren;
        this.schemaVarInstantiations = schemaVarInstantiations;
    }

    /**
     * @return The number of children in the symbolic execution taclet AST.
     */
    public int getNumChildren() {
        return numChildren;
    }

    /**
     * @return The instantiations for schema variables in the symbolic execution
     *         {@link Taclet} to be translated.
     */
    public SVInstantiations getSchemaVarInstantiations() {
        return schemaVarInstantiations;
    }

}
