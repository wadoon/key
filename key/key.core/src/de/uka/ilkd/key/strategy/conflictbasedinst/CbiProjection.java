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

    private CbiProjection() {}

    private static class CbiProjectionHolder {
        private static final CbiProjection instance = new CbiProjection();
    }

    public static CbiProjection getInstance() {
        return CbiProjectionHolder.instance;
    }

    private Term formula;
    private Sequent sequent;
    private Term result;

    @Override
    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal) {
        System.out.println("toTerm called");
        final Term formula = pos.sequentFormula().formula();
        final Sequent sequent = goal.sequent();
        final Services services = goal.proof().getServices();
        if(this.formula == formula && this.sequent == sequent) {
            return this.result;
        }
        this.sequent = sequent;
        this.formula = formula;
        result = ConflictBasedInstantiation.getInstance().findConflictingTerm(formula, sequent, pos, services);
        return result;
    }

    @Override
    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        System.out.println("filter called");
        return toTerm(app,pos,goal) != null;
    }

}
