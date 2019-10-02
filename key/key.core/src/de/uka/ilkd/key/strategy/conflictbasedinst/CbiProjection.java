package de.uka.ilkd.key.strategy.conflictbasedinst;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.feature.BinaryFeature;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;

public class CbiProjection extends BinaryFeature implements ProjectionToTerm{

    private static class CbiProjectionHolder {
        private static final CbiProjection instance = new CbiProjection();
    }

    public static CbiProjection getInstance() {
        return CbiProjectionHolder.instance;
    }

    public static void setup(boolean conflictInducing) {
        CbiServices.setInducing(conflictInducing);
    }

    private Term formula;
    private Sequent sequent;
    private Term result;

    @Override
    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal) {
        final Term formula = pos.sequentFormula().formula();
        final Sequent sequent = goal.sequent();
        final Services services = goal.proof().getServices();
        if(this.formula == formula && this.sequent == sequent) {
            return this.result;
        }
        this.sequent = sequent;
        this.formula = formula;
        CbiStatistics.startFeature(formula, InstMethod.CBI);
        result = ConflictBasedInstantiation.getInstance().findConflictingTerm(formula, sequent, pos, services);
        CbiStatistics.finishFeature(result != null);
        return result;
    }

    @Override
    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        return toTerm(app,pos,goal) != null;
    }

    public boolean solved(RuleApp app, PosInOccurrence pos, Goal goal) {
        return toTerm(app, pos, goal) != null;
    }

}
