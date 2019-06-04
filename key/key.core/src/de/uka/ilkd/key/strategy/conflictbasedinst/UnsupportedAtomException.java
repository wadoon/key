package de.uka.ilkd.key.strategy.conflictbasedinst;

import de.uka.ilkd.key.logic.Term;

public class UnsupportedAtomException extends RuntimeException {

    public UnsupportedAtomException(Term term) {
        super("Unsupported atom found: " + term.toString());
    }

}
