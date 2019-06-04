package de.uka.ilkd.key.strategy.conflictbasedinst;

import de.uka.ilkd.key.logic.op.Quantifier;

public class UnsupportedQuantifierException extends RuntimeException {

    public UnsupportedQuantifierException(Quantifier q) {
        super("Unsupported quantifier found: " + q);
    }

}
