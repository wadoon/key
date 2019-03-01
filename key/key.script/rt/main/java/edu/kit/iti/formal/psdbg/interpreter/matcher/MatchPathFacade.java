package edu.kit.iti.formal.psdbg.interpreter.matcher;

import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;

/**
 * @author Alexander Weigl
 * @version 1 (27.08.17)
 */
public class MatchPathFacade {
    public static MatchPath.MPTerm create(MatchPath<Term, ?> path, int subTerm) {
        return new MatchPath.MPTerm(path, path.getUnit().sub(subTerm), subTerm);
    }

    public static MatchPath.MPSequentFormula create(MatchPath.MPSemiSequent ss, int pos) {
        return new MatchPath.MPSequentFormula(ss, ss.getUnit().get(pos), pos);
    }

    public static MatchPath.MPSemiSequent create(MatchPath.MPSequent s, boolean antec) {
        MatchPath.MPSemiSequent mp = new MatchPath.MPSemiSequent(
                s, antec
                ? s.getUnit().antecedent()
                : s.getUnit().succedent(),
                antec);
        return mp;
    }

    public static MatchPath.MPSequent create(Sequent s) {
        return new MatchPath.MPSequent(s);
    }

    public static MatchPath.MPTerm create(MatchPath.MPSequentFormula sf) {
        return new MatchPath.MPTerm(sf, sf.getUnit().formula(), MatchPath.SEQUENT_FORMULA_ROOT);
    }

    public static MatchPath.MPSemiSequent createSuccedent(MatchPath.MPSequent sequent) {
        return create(sequent, false);
    }

    public static MatchPath.MPSemiSequent createAntecedent(MatchPath.MPSequent sequent) {
        return create(sequent, true);
    }

    /**
     * only for testing
     *
     * @param keyTerm
     * @return
     */
    public static MatchPath createRoot(Term keyTerm) {
        return new MatchPath.MPTerm(null, keyTerm, MatchPath.SEQUENT_FORMULA_ROOT);
    }

    /**
     * only for testing
     *
     * @param semiSeq
     * @return
     */
    public static MatchPath createRoot(Semisequent semiSeq) {
        return new MatchPath.MPSemiSequent(null, semiSeq, true);
    }
}
