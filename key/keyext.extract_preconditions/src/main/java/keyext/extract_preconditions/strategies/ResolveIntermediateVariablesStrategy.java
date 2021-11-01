package keyext.extract_preconditions.strategies;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.strategy.*;
import de.uka.ilkd.key.strategy.feature.CheckApplyEqFeature;
import org.key_project.util.collection.ImmutableList;

public class ResolveIntermediateVariablesStrategy implements Strategy {

    private ImmutableList<ProgramVariable> projectionVariablesList;

    public ResolveIntermediateVariablesStrategy(ImmutableList<ProgramVariable> projectionVariablesListParam) {
        projectionVariablesList = projectionVariablesListParam;
    }

    @Override
    public Name name() {
        return new Name("Resolve Intermediate Variables");
    }

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio, Goal goal) {
        if (app.rule() instanceof OneStepSimplifier) {
            return NumberRuleAppCost.getZeroCost();
        } else if ((app.rule().name().toString().equals("applyEqReverse")
            || app.rule().name().toString().equals("applyEq"))
            && !pio.subTerm().toString().equals("TRUE")
            && !pio.subTerm().toString().equals("FALSE")
            && !pio.subTerm().toString().equals("self")
            && !pio.subTerm().toString().equals("heap")
            && !pio.subTerm().toString().equals("null")) {
            return NumberRuleAppCost.create(1);
        }/* else if (app.rule().name().toString().contains("inv_axiom")) {
            return NumberRuleAppCost.create(2);
        }*/

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
        if (app.rule().name().toString().equals("applyEqReverse")
            || app.rule().name().toString().equals("applyEq")) {
            TacletApp p_app = (TacletApp) app;
            IfFormulaInstantiation ifInst = p_app.ifFormulaInstantiations ().head ();
            if (isNotSelfApplication(pio, ifInst)) {
                NoPosTacletApp applyEqReverseApp = ((NoPosTacletApp) app);
                // Term which is used to replace original variable
                SchemaVariable replaceVar;
                // Variable which is being substituted
                SchemaVariable substitutedVar;
                if (app.rule().name().toString().equals("applyEqReverse")) {
                    replaceVar =applyEqReverseApp.instantiations().lookupVar(new Name("s"));
                    substitutedVar =applyEqReverseApp.instantiations().lookupVar(new Name("t1"));
                }  else {
                    replaceVar =applyEqReverseApp.instantiations().lookupVar(new Name("t1"));
                    substitutedVar =applyEqReverseApp.instantiations().lookupVar(new Name("s"));
                }
                // This decision is more complicated than it initially seems because we need to avoid applyEq/applyEqReverse loops
                // Given an equation a=b and some appearance b...
                // This is the term which will replace an appearance of b (i.e. this term is a)
                Term replaceTerm = (Term) applyEqReverseApp.instantiations().getInstantiation(replaceVar);
                // This is the term which will be substituted on appearance (i.e. b)
                Term substitutedTerm = (Term) applyEqReverseApp.instantiations().getInstantiation(substitutedVar);
                boolean replaceTermContainsProjectionVariable = false;
                boolean substitutedTermContainsProjectionVariable = false;
                boolean replaceTermContainsSelect = false;
                boolean substitutedTermContainsSelect = false;
                for (ProgramVariable inputVar : projectionVariablesList) {
                    if (replaceTerm.toString().contains(inputVar.name().toString())) {
                        replaceTermContainsProjectionVariable=true;
                    }
                    if (substitutedTerm.toString().contains(inputVar.name().toString())) {
                        substitutedTermContainsProjectionVariable=true;
                    }
                }
                if (replaceTerm.toString().contains("select")) {
                    replaceTermContainsSelect=true;
                }
                if (substitutedTerm.toString().contains("select")) {
                    substitutedTermContainsSelect=true;
                }
                if (isConstant(substitutedTerm)) {
                    return false;
                }
                if (substitutedTermContainsProjectionVariable
                    && replaceTermContainsProjectionVariable
                    && replaceTerm.toString().length()<substitutedTerm.toString().length()) {
                    return true;
                } else if (!substitutedTermContainsProjectionVariable
                    && replaceTermContainsProjectionVariable) {
                    return true;
                } else if (!replaceTermContainsProjectionVariable
                            && !substitutedTermContainsProjectionVariable) {
                    if (substitutedTermContainsSelect
                        && replaceTermContainsSelect
                        && replaceTerm.toString().length()<substitutedTerm.toString().length()) {
                        return true;
                    }
                    if (!substitutedTermContainsSelect
                        && replaceTermContainsSelect) {
                        return true;
                    }
                }
                return false;
            } else {
                return false;
            }
                // Do not replace something with a "result" variable (would be useless)
                //!pio.sequentFormula().formula().sub(0).op().name().toString().contains("result");
        }
        return true;

    }

    private boolean isConstant(Term substitutedTerm) {
        return (substitutedTerm.op() instanceof Function &&
                    substitutedTerm.op().name().toString().equals("Z"));
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
