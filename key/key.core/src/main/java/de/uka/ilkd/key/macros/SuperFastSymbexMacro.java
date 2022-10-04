package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.prover.GoalChooser;
import de.uka.ilkd.key.prover.ProverCore;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCostCollector;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.List;
import java.util.Queue;
import java.util.function.Predicate;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (26.08.22)
 */
public class SuperFastSymbexMacro extends AbstractProofMacro {
    private static final Name[] RULESETS = new Name[]{
            new Name("simplify_prog"),
            new Name("simplify_expression"),
            new Name("simplify_autoname"),
            new Name("concrete")
    };

    @Override
    public String getName() {
        return "super-fast-symbex";
    }

    @Override
    public String getCategory() {
        return "Auto Pilot";
    }

    @Override
    public String getDescription() {
        return "A macro for doing the symbolic execution quickly. No completeness.";
    }

    @Override
    public boolean canApplyTo(@Nonnull Proof proof, @Nonnull ImmutableList<Goal> goals,
                              @Nullable PosInOccurrence posInOcc) {
        return posInOcc == null || posInOcc.isTopLevel() || containsDlTerm(posInOcc.subTerm());
    }


    @Override
    public ProofMacroFinishedInfo applyTo(@Nonnull UserInterfaceControl uic,
                                          @Nonnull Proof proof,
                                          @Nonnull ImmutableList<Goal> goals,
                                          @Nullable PosInOccurrence posInOcc,
                                          @Nullable ProverTaskListener listener) throws Exception {
        var currentStrategy = proof.getActiveStrategy();
        proof.setActiveStrategy(new SuperFastSymbexStrategy());
        ProofMacroFinishedInfo info =
                new ProofMacroFinishedInfo(this, goals, proof, false);

        final GoalChooser goalChooser = proof.getInitConfig()
                .getProfile().getSelectedGoalChooserBuilder().create();
        final ProverCore applyStrategy = new ApplyStrategy(goalChooser);
        final ImmutableList<Goal> ignoredOpenGoals = StrategyProofMacro
                .setDifference(proof.openGoals(), goals);
        applyStrategy.addProverTaskObserver(listener);

        var symbexRules = getAllowedRules(proof);
        Queue<Goal> expansionQueue = new ArrayDeque<>();
        for (var goal : goals) {
            expansionQueue.add(goal);
        }
        try {
            while (!expansionQueue.isEmpty()) {
                var goal = expansionQueue.poll();
                var newGoals = applySymbexOSS(uic, proof, goal, posInOcc, listener, symbexRules);
                for (Goal newGoal : newGoals) {
                    expansionQueue.add(newGoal);
                }
            }
        } finally {
            proof.setActiveStrategy(currentStrategy);
        }

        return info;
    }

    private List<Taclet> getAllowedRules(Proof proof) {
        Predicate<RuleSet> pred = it -> Arrays.stream(RULESETS).anyMatch(a -> a.equals(it.name()));
        return proof.getInitConfig().activatedTaclets()
                .stream()
                .filter(it -> it.getRuleSets().exists(pred))
                .collect(Collectors.toList());

    }

    private ImmutableList<Goal> applySymbexOSS(UserInterfaceControl uic, Proof proof, Goal goal,
                                               @Nullable PosInOccurrence posInOcc,
                                               @Nullable ProverTaskListener listener,
                                               List<Taclet> rules) {
        if (posInOcc == null || posInOcc.isTopLevel())
            posInOcc = findDlTermInSucc(goal);

        if (posInOcc == null) return ImmutableSLList.nil();
        goal = applyOss(uic, proof, goal, posInOcc, listener);
        return applySymbex(rules, uic, proof, goal, posInOcc, listener);
    }

    private Goal applyOss(UserInterfaceControl uic, Proof proof, Goal goal,
                          PosInOccurrence posInOcc, ProverTaskListener listener) {
        var oss = ((JavaProfile) proof.getServices().getProfile()).getOneStepSimpilifier();
        var app = oss.createApp(posInOcc.topLevel(), proof.getServices());
        var goals = oss.apply(goal, proof.getServices(), app);
        return goals.head();
    }

    private ImmutableList<Goal> applySymbex(List<Taclet> rules, UserInterfaceControl uic, Proof proof, Goal goal,
                                            PosInOccurrence posInOcc, ProverTaskListener listener) {
        for (Taclet rule : rules) {
            var find = rule.getMatcher().matchFind(posInOcc.subTerm(),
                    MatchConditions.EMPTY_MATCHCONDITIONS,
                    proof.getServices());
            var app = PosTacletApp.createPosTacletApp((FindTaclet) rule,
                    find, posInOcc, proof.getServices());
            if (app.complete() && app.isExecutable(proof.getServices())) {
                return rule.apply(goal, proof.getServices(), app);
            }
        }
        return ImmutableSLList.nil();
    }

    private PosInOccurrence findDlTermInSucc(Goal goal) {
        var formulas = goal.sequent().succedent().asList();
        for (SequentFormula formula : formulas) {
            if (containsDlTerm(formula.formula())) {
                return pioDlterm(
                        new PosInOccurrence(formula, PosInTerm.getTopLevel(), false),
                        formula.formula());
            }
        }
        return null;
    }

    private boolean containsDlTerm(Term subTerm) {
        if (subTerm.op() == Modality.BOX || subTerm.op() == Modality.DIA) {
            return true;
        }

        for (Term sub : subTerm.subs()) {
            if (containsDlTerm(sub)) return true;
        }

        return false;
    }


    private PosInOccurrence pioDlterm(PosInOccurrence cur, Term subTerm) {
        if (subTerm.op() == Modality.BOX || subTerm.op() == Modality.DIA) {
            return cur;
        }

        int i = 0;
        for (Term sub : subTerm.subs()) {
            final var pio = pioDlterm(cur.down(i++), sub);
            if (pio != null) {
                return pio;
            }
        }
        return null;
    }

}

class SuperFastSymbexStrategy implements Strategy {
    private final Name NAME = new Name(getClass().getSimpleName());

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return false;
    }

    @Override
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        return false;
    }

    @Override
    public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal, RuleAppCostCollector collector) {
    }

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        return TopRuleAppCost.INSTANCE;
    }
}