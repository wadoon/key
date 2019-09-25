package de.uka.ilkd.key.strategy.conflictbasedinst.normalization;

import java.util.LinkedList;

import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;

public class Normalizer {

    private static boolean enabled = false;

    public static void disable() {
        enabled = false;
    }

    public static void enable() {
        enabled = true;
    }

    private static Term lastTerm;
    private static Term lastNormalizedTerm;

    public static Term negatedNormalForm(Term term) {
        if(!enabled) return term;
        if(lastTerm.equals(term)) return lastNormalizedTerm;
        return null;
    }

    private static Sequent lastSequent;
    private static Sequent lastNormalizedSequent;

    public static Sequent negatedNormalForm(Sequent sequent) {
        if(!enabled) return sequent;
        if(lastSequent.equals(sequent)) return lastNormalizedSequent;
        LinkedList<SequentFormula> normAntes = new LinkedList<SequentFormula>();
        LinkedList<SequentFormula> normSuccs = new LinkedList<SequentFormula>();

        Semisequent normalizedAnte = Semisequent.EMPTY_SEMISEQUENT;
        Semisequent normalizedSucc = Semisequent.EMPTY_SEMISEQUENT;
        Sequent normalizedSequent = Sequent.createSequent(normalizedAnte, normalizedSucc);
        return null;
    }



}
