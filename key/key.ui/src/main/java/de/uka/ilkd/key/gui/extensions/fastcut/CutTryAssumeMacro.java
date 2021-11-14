package de.uka.ilkd.key.gui.extensions.fastcut;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.gui.WindowUserInterfaceControl;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.macros.AbstractProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.macros.TryCloseMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskStartedInfo;
import de.uka.ilkd.key.prover.impl.DefaultTaskFinishedInfo;
import de.uka.ilkd.key.prover.impl.DefaultTaskStartedInfo;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.TermInstantiation;
import de.uka.ilkd.key.util.SideProofUtil;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.Collections;
import java.util.concurrent.atomic.AtomicInteger;

/**
 * @author Alexander Weigl
 * @version 1 (11/14/21)
 */
public class CutTryAssumeMacro extends AbstractProofMacro {
    private static final AtomicInteger counter = new AtomicInteger();

    private static final Name CUT_TACLET_NAME = new Name("cut");
    private static final Name ASSUME_TACLET_NAME = new Name("introduceAxiom");

    @Override
    public String getName() {
        return "CutTryAssume";
    }

    @Override
    public String getCategory() {
        return "Fun";
    }

    @Override
    public String getDescription() {
        return "Cuts the proof, tries to the proof the conclusion cut branch on a side proof. " +
                "If succeed replace by an assume.";
    }

    @Override
    public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals, PosInOccurrence posInOcc) {
        return goals.size() == 1;
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Proof proof,
                                          ImmutableList<Goal> goals, PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws Exception {
        assert goals.size() == 1;
        assert uic instanceof WindowUserInterfaceControl;

        var goal = goals.head();
        var node = goal.node();

        if (posInOcc == null) {
            applyCutInteractive(uic, proof, goal, listener);
        } else {
            applyCut(uic, proof, goal, posInOcc, listener);
        }


        if (node.childrenCount() == 2) {
            //cut was applied, get instantiation
            var cutTacletApp = (NoPosTacletApp) node.getAppliedRuleApp();
            var assertCut = node.child(1);
            TermInstantiation instantiation = (TermInstantiation)
                    cutTacletApp.matchConditions().getInstantiations()
                            .lookupEntryForSV(new Name("cutFormula")).value();
            var cutFormula = instantiation.getInstantiation();
            var success = tryClose(uic, proof, proof.getGoal(assertCut), listener);
            if (success) {
                // side-proof successful, we can replace cut by assume
                proof.pruneProof(node);
                applyAssume(uic, proof, proof.getGoal(node), cutFormula, listener);
            }
        }
        return new ProofMacroFinishedInfo(this, goals);
    }


    private boolean tryClose(UserInterfaceControl uic, Proof proof, Goal goal, ProverTaskListener listener) {
        TryCloseMacro macro = new TryCloseMacro();
        var node = goal.node();
        try {
            macro.applyTo(uic, proof, ImmutableSLList.singleton(goal), null, listener);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
        return node.isClosed();
    }

    private void applyAssume(UserInterfaceControl uic, Proof proof, Goal goal, Term cutFormula,
                             ProverTaskListener listener) {
        TaskStartedInfo info = new DefaultTaskStartedInfo(TaskStartedInfo.TaskKind.Macro,
                "Proving in a side proof", 1);
        listener.taskStarted(info);
        long start = System.currentTimeMillis();

        Taclet assume = proof.getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(ASSUME_TACLET_NAME);
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(assume);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();
        app = app.addCheckedInstantiation(sv, cutFormula, proof.getServices(), true);
        goal.apply(app);

        long time = System.currentTimeMillis() - start;
        listener.taskFinished(new DefaultTaskFinishedInfo(this, null, proof, time, 1, 0));
    }

    private boolean doSideProof(Proof proof, Goal goal, ProverTaskListener listener) throws ProofInputException {
        TaskStartedInfo info = new DefaultTaskStartedInfo(TaskStartedInfo.TaskKind.Macro,
                "Proving in a side proof", 1);
        listener.taskStarted(info);
        long start = System.currentTimeMillis();

        var starter = SideProofUtil.createSideProof(proof.getEnv(), goal.sequent(),
                "Lemma" + counter.getAndIncrement());
        starter.start();
        long time = System.currentTimeMillis() - start;
        listener.taskFinished(new DefaultTaskFinishedInfo(this, null, proof, time, 1, 0));
        return starter.getProof().closed();
    }


    private void applyCut(UserInterfaceControl uic, Proof proof, Goal goal, PosInOccurrence posInOcc,
                          ProverTaskListener listener) {
        TaskStartedInfo info = new DefaultTaskStartedInfo(TaskStartedInfo.TaskKind.Macro, "Apply cut", 1);
        long start = System.currentTimeMillis();
        listener.taskStarted(info);
        Taclet cut = proof.getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(CUT_TACLET_NAME);
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();
        var t = posInOcc.subTerm();
        var tb = proof.getServices().getTermBuilder();
        var fml = t.sort() == Sort.FORMULA ? t : tb.equals(t, tb.TRUE());
        app = app.addCheckedInstantiation(sv, fml, proof.getServices(), true);
        goal.apply(app);
        long time = System.currentTimeMillis() - start;
        listener.taskFinished(new DefaultTaskFinishedInfo(this, null, proof, time, 1, 0));

    }

    private void applyCutInteractive(UserInterfaceControl uic, Proof proof, Goal goal, ProverTaskListener listener) {
        TaskStartedInfo info = new DefaultTaskStartedInfo(TaskStartedInfo.TaskKind.Macro, "Apply cut", 1);
        long start = System.currentTimeMillis();
        listener.taskStarted(info);
        Taclet cut = proof.getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(CUT_TACLET_NAME);
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);

        WindowUserInterfaceControl wuic = (WindowUserInterfaceControl) uic;
        var models = wuic.getProofControl().completeAndApplyApp(Collections.singletonList(app), goal);
        wuic.completeAndApplyTacletMatchAndWait(models, goal);

        long time = System.currentTimeMillis() - start;
        listener.taskFinished(new DefaultTaskFinishedInfo(this, null, proof, time, 1, 0));
    }
}
