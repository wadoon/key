package keyext.extract_preconditions;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.macros.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.SingleProof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import keyext.extract_preconditions.projections.AbstractTermProjection;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Class allowing the extraction of preconditions for a proof's open goals
 *
 * @author steuber
 */
public class PreconditionExtractor {
    /**
     * The proof under consideration
     */
    private final Proof proof;

    /**
     * The proof's services
     */
    private final Services proofServices;

    /**
     * User Interface Control
     */
    private final UserInterfaceControl ui;

    /**
     * The projection to apply onto the preconditions
     */
    private final AbstractTermProjection projection;

    /**
     * Generates a precondition extractor
     *
     * @param proofParam The proof to extract preconditions from
     * @param uiParam The user interface control (necessary for proof processing)
     * @param projectionParam The projection strategy to use on extracted preconditions
     *                        (this is done before the generation of the disjunction)
     */
    public PreconditionExtractor(Proof proofParam, UserInterfaceControl uiParam,
                                 AbstractTermProjection projectionParam) {
        assert (!proofParam.closed());
        this.proof = proofParam;
        this.proofServices = proof.getServices();
        this.ui = uiParam;
        this.projection = projectionParam;
    }

    /**
     * Method which extracts an overapproximate precondition for the open goals
     *
     * @return Term describing the precondition
     * @throws Exception            If Macros/Strategies throw an exception during processing
     * @throws InterruptedException If extraction is interrupted
     */
    public Term extract() throws Exception, InterruptedException {
        ImmutableList<Term> goalPreconditons = ImmutableSLList.nil();
        for (Goal currentGoal : this.proof.openGoals()) {
            goalPreconditons = goalPreconditons.append(this.extractFromGoal(currentGoal));
        }
        // Goal is missed if any of the preconditions are missed so we need an OR
        ImmutableList<Term> projectedDisjunction = ImmutableSLList.nil();
        for (Term currentTerm : goalPreconditons) {
            projectedDisjunction = projectedDisjunction.append(
                this.projection.projectTerm(currentTerm)
            );
        }
        return this.proofServices.getTermBuilder().or(projectedDisjunction);
    }

    /**
     * Generates a List of terms for a given goal.
     * <p>
     * Adapted from searchCounterexample in {@link de.uka.ilkd.key.smt.counterexample.AbstractCounterExampleGenerator}
     *
     * @param inputGoal The goal for which a precondition should be found
     * @return As we apply further Macros/Strategies to the goal before term building,
     * we could potentially obtain multiple goals and thus multiple terms for a single goal (right?)
     * @throws Exception            If Macros/Strategies throw an exception during processing
     * @throws InterruptedException If extraction is interrupted
     */
    private ImmutableList<Term> extractFromGoal(Goal inputGoal)
        throws InterruptedException, Exception {
        Proof proofCopy;
        proofCopy = this.preprocessGoal(inputGoal);
        ImmutableList<Term> goalTerms = ImmutableSLList.nil();
        for (Goal currentGoal : proofCopy.openGoals()) {
            goalTerms = goalTerms.append(sequentToPreconditionTerm(currentGoal.sequent(),
                this.proofServices));
        }
        return goalTerms;
    }

    /**
     * Preprocessing of the a goal:
     * Applies Macros/Strategies which allow an easy term transformation afterwards
     *
     * @param currentGoal Goal to apply macros/strategies on
     * @return Proof Object for Goal (copy) containing the processed goal.
     * Important: We must process <b>all</b> new open goals of this new proof object!
     * @throws Exception            If Macros/Strategies throw an exception during processing
     * @throws InterruptedException If extraction is interrupted
     */
    private Proof preprocessGoal(Goal currentGoal) throws InterruptedException, Exception {
        Proof proofCopy =
            createProof(this.proof, currentGoal.sequent(), "Proof Copy: " + this.proof.name());
        AbstractProofMacro testgenMacro = new TestGenMacro();
        testgenMacro.applyTo(this.ui, proofCopy.root(), null, null);
        // Simplification
        proofCopy.setActiveStrategy(new SimplifierStrategy());
        this.ui.getProofControl().startAndWaitForAutoMode(proofCopy);
        return proofCopy;
    }

    /**
     * Method which transforms a given sequent into a precondition producing counter examples of goal.
     * This corresponds to the precondition which produces an error at the current goal
     * I.e. AND a_i => OR b_i becomes (AND a_i) AND (AND NOT(b_i))
     *
     * @param s        Sequent to process
     * @param services Proof services
     * @return The precondition for the sequent as a term object
     */
    private static Term sequentToPreconditionTerm(Sequent s, Services services) {
        ImmutableList<Term> conjunction = ImmutableSLList.nil();

        final TermBuilder tb = services.getTermBuilder();
        conjunction = conjunction.append(tb.tt());
        for (SequentFormula f : s.antecedent()) {
            conjunction = conjunction.append(f.formula());
        }
        for (SequentFormula f : s.succedent()) {
            conjunction = conjunction.append(tb.not(f.formula()));
        }

        return tb.and(conjunction);
    }

    /**
     * Creates a copy of the proof, adapted from {@link de.uka.ilkd.key.gui.testgen.CounterExampleAction}
     *
     * @param oldProof Proof that should be copied
     * @return Creates copy from prove that can be further processed
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
