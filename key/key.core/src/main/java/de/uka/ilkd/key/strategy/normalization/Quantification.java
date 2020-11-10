package de.uka.ilkd.key.strategy.normalization;

import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;

public class Quantification {

    private final Quantifier quantifier;
    private final QuantifiableVariable quantifiedVariable;

    public Quantification(Quantifier quantifier, QuantifiableVariable quantifiedVariable) {
        this.quantifier = quantifier;
        this.quantifiedVariable = quantifiedVariable;
    }

    public Quantifier getQuantifier() {
        return this.quantifier;
    }

    public QuantifiableVariable getQuantifiedVariable() {
        return this.quantifiedVariable;
    }
}
