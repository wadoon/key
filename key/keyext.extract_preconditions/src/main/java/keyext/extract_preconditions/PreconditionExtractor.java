package keyext.extract_preconditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.SingleProof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.smt.SMTProblem;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Class allowing the extraction of preconditions for a proof's open goals
 */
public class PreconditionExtractor {
    /**
     * The proof under consideration
     */
    Proof proof;

    /**
     * The proof's services
     */
    Services proofServices;

    /**
     * Generates a precondition extractor
     * @param proofParam
     */

    public PreconditionExtractor(Proof proofParam) {
        assert (!proofParam.closed());
        this.proof = proofParam;
        this.proofServices = proof.getServices();
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
        // TODO(steuber): Add preprocessing here using (which?) Macro of testgen.
//        Proof currentProof = createProof(currentGoal.proof(),
//            currentGoal.sequent(),
//            "Blasting " + currentGoal.proof().name());
        Term result = SMTProblem.sequentToTerm(currentGoal.sequent(),
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
