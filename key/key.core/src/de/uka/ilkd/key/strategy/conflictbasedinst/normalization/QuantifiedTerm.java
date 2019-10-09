package de.uka.ilkd.key.strategy.conflictbasedinst.normalization;

import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;

public class QuantifiedTerm {

    private final Quantifier quantifier;
    private final QuantifiableVariable qv;

    public QuantifiedTerm(Quantifier quantifier, QuantifiableVariable qv) {
        this.quantifier = quantifier;
        this.qv = qv;
    }

    public Quantifier getQuantifier() {
        return quantifier;
    }

    public QuantifiableVariable getQv() {
        return qv;
    }

    @Override
    public String toString() {
        return (quantifier == Quantifier.ALL ? "all: " : "ex: ") + qv.toString();
    }



}