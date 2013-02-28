package de.uka.ilkd.key.testgeneration.core.model.implementation;

import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.smt.IllegalFormulaException;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSettings;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.AbstractSMTTranslator.Configuration;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;
import de.uka.ilkd.key.smt.SmtLib2Translator;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.testgeneration.core.model.IModelGenerator;
import de.uka.ilkd.key.testgeneration.core.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.core.model.tools.ModelGenerationTools;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.TermTransformerException;
import de.uni_freiburg.informatik.ultimate.smtinterpol.SMTInterface;

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
public enum ModelGenerator implements IModelGenerator {
    INSTANCE;

    /**
     * The solvers assigned to the ModelGenerator.
     */
    private final SolverType solver;

    /**
     * The settings for the SMT solvers. These follow a default implementation,
     * although it is possible for the user to use custom settings.
     */
    private final SMTSettings settings;

    private final Configuration configuration;

    private final SMTInterface smtInterface = SMTInterface.INSTANCE;

    /**
     * Constructs a standard model generator.
     * 
     * @param solvers
     *            the solvers to use
     * @param settings
     *            the settings for the used solvers
     */
    private ModelGenerator() {

        this.solver = SolverType.Z3_SOLVER;
        this.settings = ModelSettings.getDefaultSMTSettings();
        this.configuration = ModelSettings.getDefaultTranslatorConfiguration();
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
    private Model instantiateModel(final Model model, final String smtResult) {

        model.consumeSMTOutput(smtResult);
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

    private synchronized String solveSMTProblem(final SMTProblem problem,
            final Services services) throws ModelGeneratorException {

        try {

            String result = "";
            /*
             * Used for keeping track of the number of attempts at model
             * generation so far.
             */
            int attempts = 1;

            /*
             * Assert that we could actually find a satisfiable assignment for
             * the SMT problem. If not, keep trying until we do
             */
            do {

                String commands = translateToSMTFormat(problem.getTerm(),
                        services);

                result = smtInterface.startMessageBasedSession(commands)
                        .replaceAll("success", "").trim();

                attempts++;

            } while (!isValidResult(result)
                    && attempts < ModelSettings.getNUMBER_OF_TRIES());

            return result;

        } catch (IllegalFormulaException e) {
            throw new ModelGeneratorException(e.getMessage());
        }

    }

    private boolean isValidResult(String result) {

        /*
         * Very primitive
         */
        Pattern consPattern = Pattern.compile("\\(model");
        Matcher consMatcher = consPattern.matcher(result);
        return consMatcher.find();
    }

    private String translateToSMTFormat(Term term, Services services)
            throws IllegalFormulaException {

        /*
         * Set up the translator for this term.
         */
        SmtLib2Translator translator = new SmtLib2Translator(services,
                configuration);

        StringBuffer result = translator.translateProblem(term, services,
                settings);

        result.append("\n(get-model)");

        return result.toString();
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
    private String instantiatePathCondition(final Term pathCondition,
            final Services services) throws ModelGeneratorException {

        try {

            /*
             * Simplify the path condition. If the simplified path condition is
             * null, this means that it does not contain any primitive values.
             * There is hence nothing useful we can do with it, and we just
             * return it as null.
             */
            Term simplifiedPathCondition = ModelGenerationTools
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
    @Override
    public Model generateModel(final IExecutionNode node)
            throws ModelGeneratorException {

        try {

            Term pathCondition = node.getPathCondition();
            Services services = node.getServices();

            /*
             * Create the initial Model, without any concrete values assigned to
             * primitive integer values in it.
             */
            Model model = new TermToModelConverter().createModel(node);

            /*
             * Get concrete values for any primitive types represented in the
             * Model, extracting them from an SMT solution for the pathcondition
             * for this node.
             */
            String solverResult = instantiatePathCondition(pathCondition,
                    services);

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
        } catch (TermTransformerException e) {
            throw new ModelGeneratorException(e.getMessage());
        }
    }
}