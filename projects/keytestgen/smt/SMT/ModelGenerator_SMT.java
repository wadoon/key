package com.csvanefalk.keytestgen.core.model.implementation.SMT;

import com.csvanefalk.keytestgen.core.model.IModelGenerator;
import com.csvanefalk.keytestgen.core.model.ModelGeneratorException;
import com.csvanefalk.keytestgen.core.model.SMT.PaperTest;
import com.csvanefalk.keytestgen.core.model.implementation.Model;
import com.csvanefalk.keytestgen.core.model.implementation.ModelBuilder;
import com.csvanefalk.keytestgen.core.model.implementation.ModelVariable;
import com.csvanefalk.keytestgen.core.model.tools.ModelGenerationTools;
import com.csvanefalk.keytestgen.util.transformers.TermTransformerException;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.smt.AbstractSMTTranslator.Configuration;
import de.uka.ilkd.key.smt.IllegalFormulaException;
import de.uka.ilkd.key.smt.SMTSettings;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.SmtLib2Translator;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.SMTInterface;

import java.util.Calendar;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Given that a client does not specify anything else, KeYTestGen2 will default
 * to this implementation of {@link IModelGenerator} for the purpose of
 * instantiating path conditions.
 * <p/>
 * This particular implementation makes use of SMT solvers in order to
 * facilitate model generation. The pathcondition to be instantiated is
 * translated into the SMT-LIB2 language, and the KeY SMT interface is
 * subsequently invoked in order to find an assignment of variables that satisfy
 * the pathcondition (if such an assignment exits).
 * <p/>
 * The set of assignments found are further processed into an instance of
 * {@link IModel}, which constitutes the final representaiton of the model.
 */
public enum ModelGenerator_SMT implements IModelGenerator {
    INSTANCE;

    /**
     * The Configuration to use for the SMT-LIB2 translator used by the
     * ModelGenerator.
     */
    private final Configuration configuration;

    /**
     * The settings for the SMT solvers. These follow a default implementation,
     * although it is possible for the user to use custom settings.
     */
    private final SMTSettings settings;

    private final SMTInterface smtInterface = SMTInterface.INSTANCE;

    /**
     * Constructs a standard model generator.
     *
     * @param solvers  the solvers to use
     * @param settings the settings for the used solvers
     */
    private ModelGenerator_SMT() {

        this.settings = ModelSettings.getDefaultSMTSettings();
        this.configuration = ModelSettings.getDefaultTranslatorConfiguration();
    }

    /**
     * generates a {@link Model} for the pathcondition of a single
     * {@link IExecutionNode}, i.e. a single program statement.
     *
     * @param node     the node for which to generate a Model
     * @param mediator session mediator
     * @return the Model instance for the node
     * @throws ModelGeneratorException in the event that there was a failure to generate the Model
     */
    @Override
    public Model generateModel(final IExecutionNode node)
            throws ModelGeneratorException {

        try {

            /*
             * Extract the path condition with related KeY services.
             */
            final Term pathCondition = node.getPathCondition();
            final Services services = node.getServices();

            /*
             * Create the initial Model, without any concrete values assigned to
             * primitive integer values in it.
             */
            final Model model = new ModelBuilder().createModel(node,
                    pathCondition);

            /*
             * Get concrete values for any primitive types represented in the
             * Model, extracting them from an SMT solution for the pathcondition
             * for this node.
             */
            final String solverResult = this.instantiatePathCondition(
                    pathCondition, services);

            /*
             * If any such primitive values were found, merge their concrete
             * values into the Model
             */
            if (solverResult != null) {
                this.insertSMTOutputIntoModel(solverResult, model);
            }

            return model;

        } catch (final ProofInputException e) {
            throw new ModelGeneratorException(e.getMessage());
        } catch (final TermTransformerException e) {
            throw new ModelGeneratorException(e.getMessage());
        }
    }

    /**
     * This method takes a {@link Model} instance, and <i>instantiates</i> this
     * Model using the output of an SMT solver, here represented by
     * {@link SMTSolverResult}.
     * <p/>
     * Instantiation means that any concrete values of <i>primitive</i> values
     * represented in the Model will be extracted from the SMT solver result and
     * inserted into their respective locations in the Model. The precise
     * location of a given value instantiation is determined by the
     * <i>identifier</i> String associated with the value. A concrete value
     * belonging to a specific {@link ModelVariable} instance will have the same
     * identifier as that variable.
     *
     * @param model     the Model to instantiate
     * @param smtResult the output of an SMT solver
     * @return the instantiated Model
     * @throws ModelGeneratorException in the event that the instantiation went wrong
     */
    public void insertSMTOutputIntoModel(final String smtOutput,
                                         final Model model) throws ModelGeneratorException {

        /*
         * Break the SMT output into individual variable declarations and
         * process them separately.
         */
        final String[] definitions = smtOutput.trim().split("\\(define-fun");
        for (String definition : definitions) {

            if (!definition.isEmpty() && !definition.trim().startsWith("sat")) {

                definition = definition.trim();

                /*
                 * Extract the variable name
                 */
                final String varName = definition.substring(0,
                        definition.lastIndexOf('_'));

                /*
                 * Extract the value
                 */
                String result = "";
                boolean negFlag = false;
                for (int i = definition.indexOf(' '); i < definition.length(); i++) {

                    final char currentChar = definition.charAt(i);

                    if (!negFlag && (currentChar == '-')) {
                        negFlag = true;
                    }

                    if (Character.isDigit(currentChar)) {
                        result += currentChar;
                    }
                }

                /*
                 * Create and set the proper sign for the result.
                 */
                Integer value = Integer.parseInt(result);
                value = negFlag ? value * -1 : value;

                /*
                 * Finally, retrieve the variable corresponding to the name of
                 * the result, and insert the corresponding result into it.
                 */
                final ModelVariable variable = model.getVariable(varName.trim());
                if (variable != null) {

                    variable.setValue(value);
                } else {
                    final StringBuilder stringBuilder = new StringBuilder();
                    stringBuilder.append("Tried to insert concrete value into invalid abstract heap variable: ");
                    stringBuilder.append(varName);
                    throw new ModelGeneratorException(stringBuilder.toString());
                }
            }
        }
    }

    /**
     * Returns an {@link SMTSolverResult} for the pathcondition of a given
     * {@link IExecutionNode}. This result will represent a concrete assignment
     * of primitive values in the pathcondition, such that the constraint
     * represented by the pathcondition becomes satisifed.
     * <p/>
     * We are not interested in the shape of the solved contraint per se, rather
     * we will use these concrete values to instantiate our {@link Model}.
     *
     * @param node the node whose pathpathcondition to instantiate
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
            final Term simplifiedPathCondition = ModelGenerationTools.simplifyTerm(pathCondition);

            if (simplifiedPathCondition == null) {

                System.err.println("NULL");
                return null;

            } else {

                final String commands = this.translateToSMTLIB2(
                        simplifiedPathCondition, services);

                String result = "";
                /*
                 * Used for keeping track of the number of attempts at model
                 * generation so far.
                 */
                int attempts = 1;

                /*
                 * Assert that we could actually find a satisfiable assignment
                 * for the SMT problem. If not, keep trying until we do
                 */
                long time = Calendar.getInstance().getTimeInMillis();
                do {

                    result = this.smtInterface.startMessageBasedSession(
                            commands).replaceAll("success", "").trim();

                    attempts++;

                } while (!this.isValidResult(result)
                        && (attempts < ModelSettings.getNUMBER_OF_TRIES()));

                PaperTest.addResult(pathCondition + "_KEYNTERPOL",
                        Calendar.getInstance().getTimeInMillis() - time);
                return result;
            }

        } catch (final TermTransformerException e) {
            throw new ModelGeneratorException(e.getMessage());
        } catch (final IllegalFormulaException e) {
            throw new ModelGeneratorException(e.getMessage());
        }
    }

    /**
     * Determines if the output of the concrete integer generation process is
     * valid or not.
     *
     * @param result
     * @return
     */
    private boolean isValidResult(final String result) {

        /*
         * Very primitive
         */
        final Pattern consPattern = Pattern.compile("\\(model");
        final Matcher consMatcher = consPattern.matcher(result);
        return consMatcher.find();
    }

    /**
     * Translates a {@link Term} into the SMTLIB2 format.
     *
     * @param term
     * @param services
     * @return
     * @throws IllegalFormulaException
     */
    private String translateToSMTLIB2(final Term term, final Services services)
            throws IllegalFormulaException {

        /*
         * Set up the translator for this term.
         */
        final SmtLib2Translator translator = new SmtLib2Translator(services,
                this.configuration);

        final StringBuffer result = translator.translateProblem(term, services,
                this.settings);

        result.append("\n(get-model)");

        return result.toString();
    }
}