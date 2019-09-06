package de.uka.ilkd.key.strategy.conflictbasedinst;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

public class Skolemizer {

    private static final String SKOLEM_FUNCTION_NAME = "cbi_skolem_function_";

    private Term term;

    private Term quantors;

    private Term expression;

    private TermBuilder tb;

    private Skolemizer(Term term) {
        tb = TermBuilderHolder.getInstance().getTermBuilder();
    }

    public static Term scolemize(Term term) {
        Skolemizer sk = new Skolemizer(term);

        return null;
    }

}
