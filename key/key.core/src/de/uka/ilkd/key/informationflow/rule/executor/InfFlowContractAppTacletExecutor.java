package de.uka.ilkd.key.informationflow.rule.executor;

import org.key_project.common.core.logic.calculus.CCSequentChangeInfo;
import org.key_project.common.core.logic.calculus.PosInOccurrence;
import org.key_project.common.core.logic.calculus.SequentFormula;
import org.key_project.common.core.rule.RuleApp;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.properties.Properties;

import de.uka.ilkd.key.informationflow.rule.InfFlowContractAppTaclet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.StrategyInfoUndoMethod;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;
import de.uka.ilkd.key.rule.executor.javadl.RewriteTacletExecutor;

public class InfFlowContractAppTacletExecutor extends RewriteTacletExecutor<InfFlowContractAppTaclet> {
    /**
     * Strategy property which saves the list of formulas which where added
     * by information flow contract applications. This list is used by the
     * macros UseInformationFlowContractMacro and
     * PrepareInfFlowContractPreBranchesMacro to decide how to prepare the
     * formulas resulting from information flow contract applications.
     */
    @SuppressWarnings("unchecked")
    public static final Properties.Property<ImmutableList<Term>> INF_FLOW_CONTRACT_APPL_PROPERTY =
            new Properties.Property<ImmutableList<Term>>(
                    (Class<ImmutableList<Term>>) (Class<?>) ImmutableList.class,
                     "information flow contract applicaton property");

    
    public InfFlowContractAppTacletExecutor(InfFlowContractAppTaclet taclet) {
        super(taclet);
    }


    @Override
    protected void addToAntec(Semisequent semi,
            TermLabelState termLabelState,
            TacletLabelHint labelHint,
            CCSequentChangeInfo<Term, Sequent> currentSequent,
            PosInOccurrence<Term> pos,
            PosInOccurrence<Term> applicationPosInOccurrence,
            MatchConditions matchCond,
            Goal goal,
            RuleApp<Term, Goal> tacletApp,
            Services services) {
        final ImmutableList<SequentFormula<Term>> replacements =
                instantiateSemisequent(semi, termLabelState, labelHint, pos, matchCond, goal, tacletApp, services);
        assert replacements.size() == 1 : "information flow taclets must have " +
                "exactly one add!";
        updateStrategyInfo(services.getProof().openEnabledGoals().head(),
                replacements.iterator().next().formula());
        super.addToAntec(semi, termLabelState, labelHint, currentSequent, pos, applicationPosInOccurrence, matchCond, goal, tacletApp, services);
    }

    /**
     * Add the contract application formula to the list of the
     * INF_FLOW_CONTRACT_APPL_PROPERTY.
     * @param goal          the current goal
     * @param applFormula   the information contract application formula added
     *                      by this taclet
     */
    private void updateStrategyInfo(Goal goal, final Term applFormula) {
        ImmutableList<Term> applFormulas =
                goal.getStrategyInfo(INF_FLOW_CONTRACT_APPL_PROPERTY);
        if (applFormulas == null) {
            applFormulas = ImmutableSLList.<Term>nil();
        }
        applFormulas = applFormulas.append(applFormula);
        StrategyInfoUndoMethod undo = new StrategyInfoUndoMethod() {

            @Override
            public void undo(Properties strategyInfos) {
                ImmutableList<Term> applFormulas =
                        strategyInfos.get(INF_FLOW_CONTRACT_APPL_PROPERTY);
                strategyInfos.put(INF_FLOW_CONTRACT_APPL_PROPERTY, applFormulas.removeAll(applFormula));
            }
        };
        goal.addStrategyInfo(INF_FLOW_CONTRACT_APPL_PROPERTY, applFormulas, undo);

    }

}
