package de.uka.ilkd.key.testgeneration.model.implementation;

import java.io.File;
import java.util.Collection;
import java.util.List;

import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.gui.smt.ProofDependentSMTSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
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
import de.uka.ilkd.key.testgeneration.parsers.PathconditionTools;
import de.uka.ilkd.key.testgeneration.parsers.TermTransformerException;
import de.uka.ilkd.key.testgeneration.util.Benchmark;

/**
 * Given that a client does not specify anything else, KeYTestGen2 will default
 * to this implementation of {@link IModelGenerator} for the purpose of
 * instantiating path conditions.
 * <p>
 * This particular implementation makes use of SMT solvers in order to
 * facilitate model generation. The pathcondition to be instantiated is
 * translated into the SMT-LIB2 language, and the KeY SMT interface is
 * subsequently invoked in order to find an assignment of variables that satisfy
 * the pathcondition (if such an assignment exits).
 * <p>
 * The set of assignments found are further processed into an instance of
 * {@link IModel}, which constitutes the final representaiton of the model.
 */
public class ModelGenerator implements IModelGenerator {

    /**
     * The solvers assigned to the ModelGenerator.
     */
    private final SolverType[] solvers;

    /**
     * The settings for the SMT solvers. These follow a default implementation,
     * although it is possible for the user to use custom settings.
     */
    private final SMTSettings settings;

    /**
     * Backend constructo, used by the factory methods.
     * 
     * @param solvers
     *            the solvers to use
     * @param settings
     *            the settings for the used solvers
     */
    private ModelGenerator(SMTSettings settings, SolverType... solvers) {

        this.solvers = solvers;
        this.settings = settings;
    }

    /**
     * Creates a default implementation of the ModelGenerator, which uses the Z3
     * solvers with default settings.
     * 
     * @return a default instance of ModelGenerator
     * @throws ModelGeneratorException
     */
    public static ModelGenerator getDefaultModelGenerator() {

        return new ModelGenerator(new SMTSettings(), SolverType.Z3_SOLVER);
    }

    /**
     * Creates a custom implementation of the ModelGenerator. The user specifies
     * which SMT solvers(s) and what settings should be used
     * <p>
     * TODO: Currently only the Z3 solver will return a model, implement this
     * for the other supported solvers as well.
     * 
     * @param settings
     *            The settings for the SMT solvers used
     * @return a custom instance of the ModelGenerator
     * @throws ModelGeneratorException
     */
    public ModelGenerator getCustomModelGenerator(final SMTSettings settings,
            final SolverType... solvers) throws ModelGeneratorException {

        verifySolverAvailability(solvers);

        return new ModelGenerator(settings, solvers);
    }

    /**
     * This method takes a {@link Model} instance, and <i>instantiates</i> this
     * Model using the output of an SMT solver, here represented by
     * {@link SMTSolverResult}.
     * <p>
     * Instantiation means that any concrete values of <i>primitive</i> values
     * represented in the Model will be extracted from the SMT solver result and
     * inserted into their respective locations in the Model. The precise
     * location of a given value instantiation is determined by the
     * <i>identifier</i> String associated with the value. A concrete value
     * belonging to a specific {@link ModelVariable} instance will have the same
     * identifier as that variable.
     * 
     * @param model
     *            the Model to instantiate
     * @param smtResult
     *            the output of an SMT solver
     * @return the instantiated Model
     * @throws ModelGeneratorException
     *             in the event that the instantiation went wrong
     */
    private Model instantiateModel(Model model, SMTSolverResult smtResult) {

        String modelOutput = consolidateModelOutput(smtResult.getOutput());
        model.consumeSMTOutput(modelOutput);
        return model;
    }

    /**
     * Creates an {@link SMTProblem} from a {@link Term} representing a path
     * condition for an {@link IExecutionNode}.
     * 
     * @param targetNode
     *            the node for which to generate an SMT problem.
     * @return an SMTProblem corresponding to the path condition of the node
     * @throws ModelGeneratorException
     *             in the event that the SMT problem cannot be generated
     */
    private synchronized SMTProblem createSMTProblem(Term pathCondition)
            throws ModelGeneratorException {

        /*
         * The path condition has to be negated, in order to undo the negations
         * that will be carried out by the SMT interface.
         */
        pathCondition = TermFactory.DEFAULT.createTerm(Junctor.NOT,
                pathCondition);

        return new SMTProblem(pathCondition);

    }

    private synchronized SMTSolverResult solveSMTProblem(
            final SMTProblem problem, final Services services)
            throws ModelGeneratorException {

        SMTSolverResult result = null;

        /*
         * Assert that we could actually find a satisfiable assignment for the
         * SMT problem. If not, keep trying until we do
         */
        do {
            Benchmark.resetStopwatch();

            /*
             * Set up a SolverLauncher for the purpose of interfacing with the
             * associated SMT solvers.
             */
            SolverLauncher launcher = new SolverLauncher(settings);

            /*
             * Start the constraint solving procedure, the solution will be
             * encapsulated in the existing SMTProblem.
             */
            try {
                launcher.launch(problem, services, SolverType.Z3_SOLVER);

                result = problem.getFinalResult();

                launcher.stop();
            } catch (RuntimeException re) {

                /*
                 * In the event that the system fails due launchers being
                 * reused, dispose of them and create new ones.
                 */
                System.err.println(re.getMessage());
                re.printStackTrace();
                continue;
            }

            if (!result.isValid().equals(ThreeValuedTruth.FALSIFIABLE)) {
                System.err
                        .println("Failed to retrieve adequate SMT solution, lost "
                                + Benchmark.readStopWatch() + " milliseconds");
            }
        } while (!result.isValid().equals(ThreeValuedTruth.FALSIFIABLE));

        return result;
    }

    /**
     * Assert that the solvers associated with the ModelGenerator are
     * accessible.
     * 
     * @param solvers
     * @throws ModelGeneratorException
     */
    private static void verifySolverAvailability(SolverType... solvers)
            throws ModelGeneratorException {

        for (SolverType solver : solvers) {
            if (!solver.isInstalled(false)) {
                throw new ModelGeneratorException(
                        "Solver "
                                + solver.getName()
                                + " is not installed or could not be accessed. Check paths?");
            }
        }
    }

    /**
     * Returns an {@link SMTSolverResult} for the pathcondition of a given
     * {@link IExecutionNode}. This result will represent a concrete assignment
     * of primitive values in the pathcondition, such that the constraint
     * represented by the pathcondition becomes satisifed.
     * <p>
     * We are not interested in the shape of the solved contraint per se, rather
     * we will use these concrete values to instantiate our {@link Model}.
     * 
     * @param node
     *            the node whose pathpathcondition to instantiate
     * @return the SMT solver result
     * @throws ModelGeneratorException
     */
    private SMTSolverResult instantiatePathCondition(Term pathCondition,
            Services services) throws ModelGeneratorException {

        try {

            /*
             * Simplify the path condition. If the simplified path condition is
             * null, this means that it does not contain any primitive values.
             * There is hence nothing useful we can do with it, and we just
             * return it as null.
             */
            Term simplifiedPathCondition;

            simplifiedPathCondition = PathconditionTools
                    .simplifyTerm(pathCondition);

            if (simplifiedPathCondition == null) {
                return null;
            } else {

                /*
                 * Turn the path condition of the node into a constraint problem
                 */
                SMTProblem problem = createSMTProblem(simplifiedPathCondition);

                /*
                 * Solve the constraint and return the result
                 */
                return solveSMTProblem(problem, services);
            }

        } catch (TermTransformerException e) {
            throw new ModelGeneratorException(e.getMessage());
        }
    }

    /**
     * generates a {@link Model} for the pathcondition of a single
     * {@link IExecutionNode}, i.e. a single program statement.
     * 
     * @param node
     *            the node for which to generate a Model
     * @param mediator
     *            session mediator
     * @return the Model instance for the node
     * @throws ModelGeneratorException
     *             in the event that there was a failure to generate the Model
     */
    public IModel generateModel(IExecutionNode node, ModelMediator mediator)
            throws ModelGeneratorException {

        try {

            Term pathCondition = node.getPathCondition();
            Services services = node.getServices();

            /*
             * Create the Model
             */
            Model model = PathconditionTools.termToModel(pathCondition,
                    services, mediator);

            /*
             * Get concrete values for any primitive types represented in the
             * Model, extracting them from an SMT solution for the pathcondition
             * for this node.
             */
            SMTSolverResult solverResult = instantiatePathCondition(
                    pathCondition, services);

            /*
             * If any such primitive values were found, merge their concrete
             * values into the Model
             */
            if (solverResult != null) {
                return instantiateModel(model, solverResult);
            } else {
                return model;
            }
        } catch (ProofInputException e) {
            throw new ModelGeneratorException(e.getMessage());
        }
    }

    /**
     * Concatenates the output of the SMT solver into a single String.
     * 
     * @param output
     *            the ouput of the solver
     * @return the consolidated String
     */
    private String consolidateModelOutput(List<String> output) {

        StringBuilder stringBuilder = new StringBuilder();
        for (String substring : output) {
            stringBuilder.append(substring);
        }
        return stringBuilder.toString();
    }

    /**
     * Settings to pass to the SMT solver.
     * 
     * @author christopher
     */
    private static class SMTSettings implements de.uka.ilkd.key.smt.SMTSettings {

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

            return PathConfig.getKeyConfigDir() + File.separator
                    + "smt_formula";
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

            // return "QF_UFLIRA";
            return "AUFLIA";
        }

        @Override
        public boolean checkForSupport() {

            return false;
        }
    }

    /*
     * FIXME: BAD!
     */
    @Override
    public IModel generateModel(IExecutionNode node)
            throws ModelGeneratorException {

        return generateModel(node, null);
    }

}