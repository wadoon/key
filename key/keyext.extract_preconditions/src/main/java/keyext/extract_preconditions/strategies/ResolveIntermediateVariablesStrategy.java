package keyext.extract_preconditions.strategies;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.strategy.*;
import de.uka.ilkd.key.strategy.feature.CheckApplyEqFeature;

public class ResolveIntermediateVariablesStrategy implements Strategy {

    @Override
    public Name name() {
        return new Name("Resolve Intermediate Variables");
    }

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio, Goal goal) {

        if (app.rule() instanceof OneStepSimplifier) {
            return NumberRuleAppCost.getZeroCost();
        } else if (app.rule().name().toString().equals("applyEqReverse")
            && !pio.subTerm().toString().equals("TRUE")
            && !pio.subTerm().toString().equals("FALSE")
            && !pio.subTerm().toString().equals("self")
            && !pio.subTerm().toString().equals("heap")
            && !pio.subTerm().toString().equals("null")) {
            return NumberRuleAppCost.create(1);
        }

        return TopRuleAppCost.INSTANCE;
    }

    @Override
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {

        /*if (app.rule() instanceof OneStepSimplifier) {
            return true;
        }*/
        /*if (CheckApplyEqFeature.INSTANCE.computeCost(app, pio, goal)==CheckApplyEqFeature.ZERO_COST) {
            System.out.println("APPLY");
            System.out.println(pio.sequentFormula());

            return true;
        } else {
            return false;
        }*/
        if (app.rule().name().toString().equals("applyEqReverse")) {
            TacletApp p_app = (TacletApp) app;
            IfFormulaInstantiation ifInst = p_app.ifFormulaInstantiations ().head ();
            return isNotSelfApplication(pio, ifInst);
        }
        return true;

    }

    // Modified version from CheckApplyEqFeature:
    // ApplyEq(Reverse) must not be applied to the defining equation itself
    private boolean isNotSelfApplication(PosInOccurrence pos,
                                         IfFormulaInstantiation ifInst) {
        if ( ! ( ifInst instanceof IfFormulaInstSeq )
            || ifInst.getConstrainedFormula () != pos.sequentFormula ()
            || ( (IfFormulaInstSeq)ifInst ).inAntec () != pos.isInAntec () )
            return true;

        // Position may not be one of the terms compared in
        // the equation

        final PIOPathIterator it = pos.iterator ();

        it.next ();

        // leading updates are not interesting
        while ( it.getSubTerm ().op () instanceof UpdateApplication) {
            if ( !it.hasNext () ) return true;
            it.next ();
        }

        if ( ! ( it.getSubTerm ().op () instanceof Equality) || !it.hasNext () )
            return true;

        return false;
    }

    @Override
    public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
                               RuleAppCostCollector collector) {
        System.out.println("Instantiate:");
        System.out.println(app.rule().name().toString());
    }

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return false;
    }

}
