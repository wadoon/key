package keyext.extract_preconditions;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.macros.SemanticsBlastingMacro;
import de.uka.ilkd.key.macros.TestGenMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.SingleProof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo;
import de.uka.ilkd.key.prover.impl.DefaultTaskStartedInfo;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.util.Debug;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Class allowing the extraction of preconditions for a proof's open goals
 */
public class PreconditionExtractor {
    /**
     * The proof under consideration
     */
    private Proof proof;

    /**
     * The proof's services
     */
    private Services proofServices;

    /**
     * User Interface Control
     */
    private UserInterfaceControl ui;

    /**
     * Generates a precondition extractor
     *
     * @param proofParam
     */

    public PreconditionExtractor(Proof proofParam, UserInterfaceControl uiParam) {
        assert (!proofParam.closed());
        this.proof = proofParam;
        this.proofServices = proof.getServices();
        this.ui = uiParam;
    }

    public Term extract() {
        ImmutableList<Term> goalPreconditons = ImmutableSLList.nil();
        for (Goal currentGoal : this.proof.openGoals()) {
            goalPreconditons = goalPreconditons.append(this.extractFromGoal(currentGoal));
        }
        // Goal is missed if any of the preconditions are missed so we need an OR
        return this.proofServices.getTermBuilder().or(goalPreconditons);
    }

    /**
     * Generates ??? for a given goal
     * Adapted from searchCounterexample in {@link de.uka.ilkd.key.smt.counterexample.AbstractCounterExampleGenerator}
     *
     * @param currentGoal The goal for which a precondition should be found
     */
    private Term extractFromGoal(Goal currentGoal) {
        Proof proofCopy =
            createProof(this.proof, currentGoal.sequent(), "Proof Copy: " + this.proof.name());
        //final SemanticsBlastingMacro macro = new SemanticsBlastingMacro();
        final TestGenMacro macro = new TestGenMacro();
        TaskFinishedInfo info = ProofMacroFinishedInfo.getDefaultInfo(macro, proof);
        final ProverTaskListener ptl = this.ui.getProofControl().getDefaultProverTaskListener();
        ptl.taskStarted(
            new DefaultTaskStartedInfo(TaskStartedInfo.TaskKind.Macro, macro.getName(), 0));

        try {
            info = macro.applyTo(this.ui, proof, ImmutableSLList.singleton(currentGoal), null, ptl);
        } catch (InterruptedException e) {
            Debug.out("Semantics blasting interrupted");
        } finally {
            ptl.taskFinished(info);
        }
        Term result = SMTProblem.sequentToTerm(proofCopy.root().sequent(),
            this.proofServices);
        return result;
    }

    /**
     * Creates a copy of the proof, adapted from {@link de.uka.ilkd.key.gui.testgen.CounterExampleAction}
     *
     * @param oldProof Proof that should be copied
     * @return
     */
    private Proof createProof(Proof oldProof, Sequent oldSequent, String proofName) {
        Sequent newSequent = createNewSequent(oldSequent);
        InitConfig newInitConfig = oldProof.getInitConfig().deepCopy();
        Proof proof = new Proof(proofName,
            newSequent, "",
            newInitConfig.createTacletIndex(),
            newInitConfig.createBuiltInRuleIndex(),
            newInitConfig);

        proof.setEnv(oldProof.getEnv());
        proof.setNamespaces(oldProof.getNamespaces());

        ProofAggregate pa = new SingleProof(proof, "XXX");

        // ui.registerProofAggregate(pa);

        SpecificationRepository spec = proof.getServices().getSpecificationRepository();
        spec.registerProof(spec.getProofOblInput(oldProof), proof);

        // mediator.goalChosen(proof.getGoal(proof.root()));

        return proof;
    }

    /**
     * Creates the {@link Sequent} for the new {@link Proof}.
     * Taken from {@link de.uka.ilkd.key.smt.counterexample.AbstractCounterExampleGenerator}
     *
     * @param oldSequent The {@link Sequent} to find a counter example for.
     * @return The new {@link Sequent}.
     */
    protected Sequent createNewSequent(Sequent oldSequent) {
        return Sequent.createSequent(oldSequent.antecedent(), oldSequent.succedent());
    }
}
