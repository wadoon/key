/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.informationflow.macros;

import java.util.Map;
import java.util.Set;

import org.key_project.common.core.logic.calculus.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.macros.AbstractProofMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.InfFlowProgVarRenamer;


/**
 *
 * @author christoph
 */
public abstract class AbstractFinishAuxiliaryComputationMacro extends AbstractProofMacro {

    @Override
    public String getName() {
        return "Finish auxiliary computation";
    }

    @Override
    public String getCategory() {
        return "Auxiliary Computation";
    }

    @Override
    public String getDescription() {
        return "Finish auxiliary computation.";
    }

    static JavaDLTerm calculateResultingTerm(Proof proof,
                                       IFProofObligationVars ifVars,
                                       Goal initGoal) {
        final JavaDLTerm[] goalFormulas1 =
                buildExecution(ifVars.c1, ifVars.getMapFor(ifVars.c1),
                               proof.openGoals(), initGoal);
        final JavaDLTerm[] goalFormulas2 =
                buildExecution(ifVars.c2, ifVars.getMapFor(ifVars.c2),
                               proof.openGoals(), initGoal);
        final TermBuilder tb = proof.getServices().getTermBuilder();
        JavaDLTerm composedStates = tb.ff();
        for (int i = 0; i < goalFormulas1.length; i++) {
            for (int j = i; j < goalFormulas2.length; j++) {
                final JavaDLTerm composedState = tb.and(goalFormulas1[i], goalFormulas2[j]);
                composedStates = tb.or(composedStates, composedState);
            }
        }
        return composedStates;
    }

    private static JavaDLTerm[] buildExecution(ProofObligationVars c,
                                         Map<JavaDLTerm, JavaDLTerm> vsMap,
                                         ImmutableList<Goal> symbExecGoals,
                                         Goal initGoal) {
        Services services = initGoal.proof().getServices();
        final JavaDLTerm[] goalFormulas = buildFormulasFromGoals(symbExecGoals);
        final InfFlowProgVarRenamer renamer =
                        new InfFlowProgVarRenamer(goalFormulas, vsMap,
                                                  c.postfix, initGoal, services);
        final JavaDLTerm[] renamedGoalFormulas =
                renamer.renameVariablesAndSkolemConstants();
        JavaDLTerm[] result = new JavaDLTerm[renamedGoalFormulas.length];
        final TermBuilder tb = services.getTermBuilder();
        for (int i = 0; i < renamedGoalFormulas.length; i++) {
            result[i] =
                    tb.applyElementary(c.pre.heap, renamedGoalFormulas[i]);
        }
        return result;
    }

    private static JavaDLTerm[] buildFormulasFromGoals(ImmutableList<Goal> symbExecGoals) {
        JavaDLTerm[] result = new JavaDLTerm[symbExecGoals.size()];
        int i = 0;
        for (final Goal symbExecGoal : symbExecGoals) {
            result[i] = buildFormulaFromGoal(symbExecGoal);
            i++;
        }
        return result;
    }

    private static JavaDLTerm buildFormulaFromGoal(Goal symbExecGoal) {
        final TermBuilder tb = symbExecGoal.proof().getServices().getTermBuilder();
        JavaDLTerm result = tb.tt();
        for (final SequentFormula<JavaDLTerm> f : symbExecGoal.sequent().antecedent()) {
            result = tb.and(result, f.formula());
        }
        for (final SequentFormula<JavaDLTerm> f : symbExecGoal.sequent().succedent()) {
            result = tb.and(result, tb.not(f.formula()));
        }
        return result;
    }

    protected static void addContractApplicationTaclets(Goal initiatingGoal,
                                                        Proof symbExecProof) {
        final ImmutableList<Goal> openGoals = symbExecProof.openGoals();
        for (final Goal openGoal : openGoals) {
            final Set<NoPosTacletApp> ruleApps =
                    openGoal.indexOfTaclets().allNoPosTacletApps();
            for (final NoPosTacletApp ruleApp : ruleApps) {
                final Taclet t = ruleApp.taclet();
                if (t.getSurviveSymbExec()) {
                    initiatingGoal.addTaclet(t, SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
                }
            }
        }
    }
}