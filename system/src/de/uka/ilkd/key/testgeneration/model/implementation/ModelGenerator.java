package de.uka.ilkd.key.testgeneration.model.implementation;

import java.io.File;
import java.text.ParseException;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;

import z3parser.api.Z3ModelParser.ValueContainer;
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
import de.uka.ilkd.key.testgeneration.parsers.PathconditionParser;
import de.uka.ilkd.key.testgeneration.visitors.TermModelVisitor;

/**
 * Given that a client does not specify anything else, KeYTestGen2 will default to this
 * implementation of {@link IModelGenerator} for the purpose of instantiating path conditions.
 * <p>
 * This particular implementation makes use of SMT solvers in order to facilitate model generation.
 * The pathcondition to be instantiated is translated into the SMT-LIB2 language, and the KeY SMT
 * interface is subsequently invoked in order to find an assignment of variables that satisfy the
 * pathcondition (if such an assignment exits).
 * <p>
 * The set of assignments found are further processed into an instance of {@link IModel}, which
 * constitutes the final representaiton of the model.
 */
public class ModelGenerator
        implements IModelGenerator {

    /**
     * The solvers assigned to the ModelGenerator.
     */
    private final SolverType[] solvers;

    /**
     * The settings for the SMT solvers. These follow a default implementation, although it is
     * possible for the user to use custom settings.
     */
    private final SMTSettings settings;

    /**
     * ConditionParser for the purpose of simplifying path conditions.
     */
    private final PathconditionParser conditionParser = new PathconditionParser();

    /**
     * Backend constructor for the factory methods
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
     * Creates a default implementation of the ModelGenerator, which uses the Z3 solvers with
     * default settings.
     * 
     * @return a default instance of ModelGenerator
     * @throws ModelGeneratorException
     */
    public static IModelGenerator getDefaultModelGenerator()
            throws ModelGeneratorException {

        verifySolverAvailability(SolverType.Z3_SOLVER);

        return new ModelGenerator(new SMTSettings(), SolverType.Z3_SOLVER);
    }

    /**
     * Creates a custom implementation of the ModelGenerator. The user specifies which SMT
     * solvers(s) and what settings should be used TODO Currently only the Z3 solver will return a
     * model, implment this for the other supported solvers as well
     * 
     * @param settings
     *            The settings for the SMT solvers used
     * @return a custom instance of the ModelGenerator
     * @throws ModelGeneratorException
     */
    public ModelGenerator getCustomModelGenerator(
            final SMTSettings settings,
            final SolverType... solvers) throws ModelGeneratorException {

        verifySolverAvailability(solvers);

        return new ModelGenerator(settings, solvers);
    }

    /**
     * Generates a model satisfying the pathcondition for a given {link {@link IExecutionNode}. The
     * model is encoded in XML format, and serves as a basis for creating executable test suites.
     * 
     * @param targetNode
     *            the node whose path condition we wish to find a model for
     * @param services
     *            related to the underlying implementation. See {@link Services}
     * @return the model for the path condition, in XML format
     * @throws ModelGeneratorException
     */
    public String generateNodeModel(
            final IExecutionNode targetNode,
            final Services services) throws ModelGeneratorException {

        /*
         * Turn the path condition of the node into a constraint problem
         */
        SMTProblem problem = createSMTProblem(targetNode);

        /*
         * Solve the constraint
         */
        SMTSolverResult result = solveSMTProblem(problem, services);

        /*
         * Return the model satisfying the constraint
         */
        // return createModel(result);
        return null;
    }

    private IModel createModel(IExecutionNode node, SMTSolverResult result)
            throws ParseException, ModelGeneratorException {

        try {

            /*
             * Extract the variables in the partial heap state
             */
            TermModelVisitor termModelVisitor = new TermModelVisitor(node.getServices());
            node.getPathCondition().execPostOrder(termModelVisitor);
            List<ModelVariable> modelVariables = termModelVisitor.getModelSkeleton();

            /*
             * Extract the heap state interpretation using the Z3 parser.
             */
            String modelOutput = consolidateModelOutput(result.getOutput());
            HashMap<String, z3parser.api.Z3ModelParser.ValueContainer> rawModel =
                    z3parser.api.Z3ModelParser.parseModel(modelOutput);

            /*
             * Insert the generated values into the partial heapstate
             */
            for (ValueContainer container : rawModel.values()) {
                for(ModelVariable modelVariable : modelVariables) {
                    if(modelVariable.getId().equals(container.getName())) {
                        modelVariable.setValue(container.getValue());
                    }
                }
            }
            
            /*
             * Finally, turn the partial heapstate into a full-fledged Model
             */
            Model finalModel = new Model();
            for(ModelVariable modelVariable : modelVariables) {
                finalModel.add(modelVariable);
            }

            return finalModel;

        }
        catch (ProofInputException pie) {
            throw new ModelGeneratorException(pie.getMessage());
        }
    }

    /**
     * Encapsulates the path condition of the {@code targetNode} in an {@link SMTProblem}, which can
     * in be passed to external SMT solvers.
     * 
     * @param the
     *            target path condition
     * @return an SMTProblem corresponding to the path condition
     * @throws ModelGeneratorException
     */
    private synchronized SMTProblem createSMTProblem(final IExecutionNode targetNode)
            throws ModelGeneratorException {

        try {

            Term pathCondition = targetNode.getPathCondition();

            /*
             * Simplify the path condition
             */
            Term simplifiedPathCondition = conditionParser.simplifyTerm(pathCondition);

            /*
             * The path condition has to be negated, in order to undo the negations that will be
             * carried out by the SMT interface.
             */
            simplifiedPathCondition =
                    TermFactory.DEFAULT.createTerm(Junctor.NOT, simplifiedPathCondition);

            return new SMTProblem(simplifiedPathCondition);

        }
        catch (ProofInputException e) {

            throw new ModelGeneratorException("It was not possible to generate an SMT Problem: "
                    + e.getMessage());
        }
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

            /*
             * Set up a SolverLauncher for the purpose of interfacing with the associated SMT
             * solvers.
             */
            SolverLauncher launcher = new SolverLauncher(settings);

            /*
             * Start the constraint solving procedure, the solution will be encapsulated in the
             * existing SMTProblem.
             */
            try {

                launcher.launch(problem, services, SolverType.Z3_SOLVER);

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
        }

        while (!result.isValid().equals(ThreeValuedTruth.FALSIFIABLE));

        return result;
    }

    /**
     * Assert that the solvers associated with the ModelGenerator are accessible.
     * 
     * @param solvers
     * @throws ModelGeneratorException
     */
    private static void verifySolverAvailability(SolverType... solvers)
            throws ModelGeneratorException {

        for (SolverType solver : solvers) {
            if (!solver.isInstalled(false)) {
                throw new ModelGeneratorException("Solver " + solver.getName()
                        + " is not installed or could not be accessed. Check paths?");
            }
        }
    }

    @Override
    public IModel generateModel(IExecutionNode node) throws ModelGeneratorException {

        /*
         * Turn the path condition of the node into a constraint problem
         */
        SMTProblem problem = createSMTProblem(node);

        /*
         * Solve the constraint
         */
        SMTSolverResult result = solveSMTProblem(problem, node.getServices());

        /*
         * Return the model satisfying the constraint
         */
        try {
            return createModel(node, result);
        }
        catch (ParseException e) {
            throw new ModelGeneratorException(e.getMessage()
                    + "\nThe defunct model is:\n"
                    + consolidateModelOutput(result.getOutput()));
        }
    }

    private String consolidateModelOutput(List<String> output) {

        StringBuilder stringBuilder = new StringBuilder();
        for (String substring : output) {
            stringBuilder.append(substring);
        }
        return stringBuilder.toString();
    }

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

            return "AUFLIA";
        }

        @Override
        public boolean checkForSupport() {

            return false;
        }
    }

}