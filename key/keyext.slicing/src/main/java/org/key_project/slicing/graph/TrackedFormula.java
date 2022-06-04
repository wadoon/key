package org.key_project.slicing.graph;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.pp.LogicPrinter;
import org.key_project.util.collection.ImmutableList;

import java.util.Objects;

/**
 * A sequent formula tracked by the dependency graph.
 * The position in the sequent (antecedent / succedent)
 * and the position in the proof tree (branch location) are also stored.
 *
 * @author Arne Keller
 */
public class TrackedFormula implements GraphNode {
    /**
     * Symbol used to indicate the position of the formula in the sequent.
     *
     * @see #toString(boolean)
     */
    private static final String SEQ_ARROW = "⟹";

    /**
     * The formula.
     */
    public final SequentFormula formula;
    /**
     * Location in the proof tree.
     */
    public final ImmutableList<String> branchLocation; // TODO: introduce a proper class for this?
    /**
     * Whether the formula is in the antecedent.
     */
    public final boolean inAntec;
    /**
     * Services object (required to print the formula).
     */
    public final Services services;

    public TrackedFormula(
            SequentFormula formula,
            ImmutableList<String> branchLocation,
            boolean inAntec,
            Services services
    ) {
        this.formula = formula;
        this.branchLocation = branchLocation;
        this.inAntec = inAntec;
        this.services = services;
    }

    @Override
    public String toString(boolean abbreviated) {
        if (abbreviated) {
            return Integer.toHexString(hashCode());
        }
        String input = LogicPrinter.quickPrintTerm(
                formula.formula(),
                services,
                true, // pretty print
                true // using unicode symbols
        ).trim();
        var id = input + branchLocation.stream().reduce("", String::concat);
        return !inAntec ? (SEQ_ARROW + " " + id) : (id + " " + SEQ_ARROW);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        TrackedFormula that = (TrackedFormula) o;
        return inAntec == that.inAntec
                && Objects.equals(formula, that.formula)
                && Objects.equals(branchLocation, that.branchLocation);
    }

    @Override
    public int hashCode() {
        return Objects.hash(formula, branchLocation, inAntec);
    }

    @Override
    public ImmutableList<String> branch() {
        return branchLocation;
    }
}
