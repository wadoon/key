package de.uka.ilkd.key.keynterpol;

import java.io.File;
import java.text.ParseException;
import java.util.Collection;
import java.util.HashMap;

import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.gui.smt.ProofDependentSMTSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.testgeneration.model.IModel;
import de.uka.ilkd.key.testgeneration.model.IModelGenerator;
import de.uka.ilkd.key.testgeneration.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.model.implementation.Model;
import de.uka.ilkd.key.testgeneration.model.implementation.ModelVariable;
import de.uka.ilkd.key.testgeneration.parsers.PathconditionParser;
import de.uka.ilkd.key.testgeneration.util.Benchmark;

public class EmbeddedModelGenerator
        implements IModelGenerator {

    /**
     * generates a {@link Model} for the pathcondition of a single {@link IExecutionNode}, i.e. a
     * single program statement.
     * 
     * @param node
     *            the node for which to generate a Model
     * @return the Model instance for the node
     * @throws ModelGeneratorException
     *             in the event that there was a failure to generate the Model
     */
    @Override
    public IModel generateModel(IExecutionNode node) throws ModelGeneratorException {

        try {

            /*
             * Create the skeletal model (no concrete values for primitive types).
             */
            Term pathCondition = node.getPathCondition();
            Services services = node.getServices();
            Model model = PathconditionParser.createModel(pathCondition, services);

            /*
             * Get concrete values for any primitive types represented in the Model, extracting them
             * from an SMT solution for the pathcondition for this node.
             */
            resolveConcreteValues(pathCondition, services);

            return model;
        }
        catch (ProofInputException e) {
            throw new ModelGeneratorException(e.getMessage());
        }
    }

    /**
     * Returns an {@link SMTSolverResult} for the pathcondition of a given {@link IExecutionNode}.
     * This result will represent a concrete assignment of primitive values in the pathcondition,
     * such that the constraint represented by the pathcondition becomes satisifed.
     * <p>
     * We are not interested in the shape of the solved contraint per se, rather we will use these
     * concrete values to instantiate our {@link Model}.
     * 
     * @param node
     *            the node whose pathpathcondition to instantiate
     * @return the SMT solver result
     * @throws ModelGeneratorException
     */
    private void resolveConcreteValues(Term pathCondition, Services services)
            throws ModelGeneratorException {

        /*
         * Simplify the path condition. If the simplified path condition is null, this means that it
         * does not contain any primitive values. There is hence nothing useful we can do with it,
         * and we just return it as null.
         */
        Term simplifiedPathcondition = PathconditionParser.simplifyTerm(pathCondition);
        if (simplifiedPathcondition == null) {
            return;
        }

        /*
         * Turn the path condition of the node into a constraint problem
         */
        SMTProblem problem = createSMTProblem(simplifiedPathcondition);

        /*
         * Solve the constraint.
         */
        SMTSolverResult result = solveSMTProblem(problem, services);
    }

    /**
     * Creates an {@link SMTProblem} from a {@link Term} representing a path condition for an
     * {@link IExecutionNode}.
     * 
     * @param targetNode
     *            the node for which to generate an SMT problem.
     * @return an SMTProblem corresponding to the path condition of the node
     * @throws ModelGeneratorException
     *             in the event that the SMT problem cannot be generated
     */
    private synchronized SMTProblem createSMTProblem(final Term pathCondition)
            throws ModelGeneratorException {

        /*
         * Simplify the path condition
         */
        Term simplifiedPathCondition = PathconditionParser.simplifyTerm(pathCondition);

        /*
         * The path condition has to be negated, in order to undo the negations that will be carried
         * out by the SMT interface.
         */
        simplifiedPathCondition =
                TermFactory.DEFAULT.createTerm(Junctor.NOT, simplifiedPathCondition);

        return new SMTProblem(simplifiedPathCondition);

    }

    private synchronized SMTSolverResult solveSMTProblem(
            final SMTProblem problem,
            final Services services) throws ModelGeneratorException {

        SMTSolverResult result = null;

        /*
         * Assert that we could actually find a satisfiable assignment for the SMT problem. If not,
         * keep trying until we do
         */
        do {
            Benchmark.resetStopwatch();

            /*
             * Set up a SolverLauncher for the purpose of interfacing with the associated SMT
             * solvers.
             */
            SMTSettings settings = new SMTSettings();
            SolverLauncher launcher = new SolverLauncher(settings);

            /*
             * Start the constraint solving procedure, the solution will be encapsulated in the
             * existing SMTProblem.
             */
            try {
                launcher.launch(problem, services, SolverType.KeYnterpol);

                result = problem.getFinalResult();

                launcher.stop();
            }
            catch (RuntimeException re) {

                /*
                 * In the event that the system fails due launchers being reused, dispose of them
                 * and create new ones.
                 */
                System.err.println(re.getMessage());
                re.printStackTrace();
                continue;
            }

            if (!result.isValid().equals(ThreeValuedTruth.FALSIFIABLE)) {
                System.err.println("Failed to retrieve adequate SMT solution, lost "
                        + Benchmark.readStopWatch() + " milliseconds");
            }
        }
        while (!result.isValid().equals(ThreeValuedTruth.FALSIFIABLE));

        return result;
    }

    /**
     * Settings to pass to the SMT solver.
     * 
     * @author christopher
     */
    private static class SMTSettings
            implements de.uka.ilkd.key.smt.SMTSettings {

        @Override
        public int getMaxConcurrentProcesses() {

            return 1;
        }

        @Override
        public int getMaxNumberOfGenerics() {

            return 2;
        }

        @Override
        public String getSMTTemporaryFolder() {

            return PathConfig.getKeyConfigDir() + File.separator + "smt_formula";
        }

        @Override
        public Collection<Taclet> getTaclets() {

            return null;
        }

        @Override
        public long getTimeout() {

            return 5000;
        }

        @Override
        public boolean instantiateNullAssumption() {

            return true;
        }

        @Override
        public boolean makesUseOfTaclets() {

            return false;
        }

        @Override
        public boolean useExplicitTypeHierarchy() {

            return false;
        }

        @Override
        public boolean useBuiltInUniqueness() {

            return false;
        }

        @Override
        public boolean useAssumptionsForBigSmallIntegers() {

            return false;
        }

        @Override
        public boolean useUninterpretedMultiplicationIfNecessary() {

            return false;
        }

        @Override
        public long getMaximumInteger() {

            return ProofDependentSMTSettings.getDefaultSettingsData().maxInteger;
        }

        @Override
        public long getMinimumInteger() {

            return ProofDependentSMTSettings.getDefaultSettingsData().minInteger;
        }

        @Override
        public String getLogic() {

            return "QF_UFLIRA";
        }

        @Override
        public boolean checkForSupport() {

            return false;
        }
    }

}
