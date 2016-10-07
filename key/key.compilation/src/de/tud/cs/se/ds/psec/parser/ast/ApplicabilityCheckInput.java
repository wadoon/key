package de.tud.cs.se.ds.psec.parser.ast;

import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.uka.ilkd.key.rule.Taclet;

/**
 * A container class for inputs that are relevant for assessing the
 * applicability of a translation rule.
 *
 * @author Dominic Scheurer
 */
public class ApplicabilityCheckInput {

    private int numChildren;
    private RuleInstantiations instantiations;

    /**
     * @param numChildren
     *            The number of children in the symbolic execution taclet AST.
     * @param schemaVarInstantiations
     *            The instantiations for schema variables in the symbolic
     *            execution {@link Taclet} to be translated.
     */
    public ApplicabilityCheckInput(int numChildren,
            RuleInstantiations instantiations) {
        this.numChildren = numChildren;
        this.instantiations = instantiations;
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
    public RuleInstantiations getInstantiations() {
        return instantiations;
    }

}
