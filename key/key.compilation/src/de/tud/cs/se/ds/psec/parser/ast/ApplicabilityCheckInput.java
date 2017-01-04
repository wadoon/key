package de.tud.cs.se.ds.psec.parser.ast;

import org.objectweb.asm.Label;

import de.tud.cs.se.ds.psec.compiler.GlobalLabelHelper;
import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.Rule;
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
    private GlobalLabelHelper globalLabelHelper;
    private Services services;

    /**
     * @param numChildren
     *            The number of children in the symbolic execution taclet AST.
     * @param instantiations
     *            The instantiations for schema variables in the symbolic
     *            execution {@link Rule} to be translated.
     * @param globalLabelHelper
     *            TODO
     * @param services
     *            The {@link Services} object.
     */
    public ApplicabilityCheckInput(int numChildren,
            RuleInstantiations instantiations,
            GlobalLabelHelper globalLabelHelper, Services services) {
        this.numChildren = numChildren;
        this.instantiations = instantiations;
        this.globalLabelHelper = globalLabelHelper;
        this.services = services;
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

    /**
     * @return The {@link GlobalLabelHelper} for retrieving information about
     *         global {@link Label}s.
     */
    public GlobalLabelHelper getGlobalLabelHelper() {
        return globalLabelHelper;
    }

    /**
     * @return The {@link Services} object.
     */
    public Services getServices() {
        return services;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append(ApplicabilityCheckInput.class.getSimpleName()).append("(")
                .append("numChildren=").append(numChildren)
                .append(", instantiations=").append(instantiations).append(")");

        return sb.toString();
    }

}
