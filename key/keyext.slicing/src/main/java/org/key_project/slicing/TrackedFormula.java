package org.key_project.slicing;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.pp.LogicPrinter;
import org.key_project.util.collection.ImmutableList;

import java.util.Objects;

public class TrackedFormula {
    public SequentFormula formula;
    public ImmutableList<String> branchLocation;
    public boolean inAntec;
    public Services services;

    private static final String SEQ_ARROW = "⟹";

    public TrackedFormula(SequentFormula formula, ImmutableList<String> branchLocation, boolean inAntec, Services services) {
        this.formula = formula;
        this.branchLocation = branchLocation;
        this.inAntec = inAntec;
        this.services = services;
    }

    @Override
    public String toString() {
        String input = LogicPrinter.quickPrintTerm(formula.formula(), services, true, true).trim();
        var id = input + branchLocation.stream().reduce("", String::concat);
        return !inAntec ? (SEQ_ARROW + " " + id) : (id + " " + SEQ_ARROW);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        TrackedFormula that = (TrackedFormula) o;
        return inAntec == that.inAntec && Objects.equals(formula, that.formula) && Objects.equals(branchLocation, that.branchLocation);
    }

    @Override
    public int hashCode() {
        return Objects.hash(formula, branchLocation, inAntec);
    }
}
