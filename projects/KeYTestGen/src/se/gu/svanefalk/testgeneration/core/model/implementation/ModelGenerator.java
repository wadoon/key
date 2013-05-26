package se.gu.svanefalk.testgeneration.core.model.implementation;

import java.util.Map;

import se.gu.svanefalk.testgeneration.core.model.IModelGenerator;
import se.gu.svanefalk.testgeneration.core.model.ModelGeneratorException;
import se.gu.svanefalk.testgeneration.core.model.tools.ModelGenerationTools;
import se.gu.svanefalk.testgeneration.keystone.KeYStone;
import se.gu.svanefalk.testgeneration.keystone.KeYStoneException;
import se.gu.svanefalk.testgeneration.util.transformers.NormalizeArithmeticComparatorsTransformer;
import se.gu.svanefalk.testgeneration.util.transformers.TermTransformerException;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.smt.AbstractSMTTranslator.Configuration;
import de.uka.ilkd.key.smt.SMTSettings;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

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

    private static ModelGenerator instance = null;

    public static ModelGenerator getInstance() {
        if (ModelGenerator.instance == null) {
            ModelGenerator.instance = new ModelGenerator();
        }
        return ModelGenerator.instance;
    }

    KeYStone keYStone = KeYStone.getInstance();

    /**
     * Constructs a standard model generator.
     * 
     * @param solvers
     *            the solvers to use
     * @param settings
     *            the settings for the used solvers
     */
    private ModelGenerator() {

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

            /*
             * Extract the path condition with related KeY services.
             */
            final Term pathCondition = node.getPathCondition();
            final Services services = node.getServices();

            /*
             * Create the initial Model, without any concrete values assigned to
             * primitive integer values in it.
             */
            final Model model = new TermToModelConverter().createModel(node);

            /*
             * Complete the model with concrete integer values.
             */
            final Map<String, Integer> concreteValues = getConcreteValues(
                    pathCondition, services);

            instantiateModel(model, concreteValues);

            return model;

        } catch (final ProofInputException e) {
            throw new ModelGeneratorException(e.getMessage());
        } catch (final TermTransformerException e) {
            throw new ModelGeneratorException(e.getMessage());
        }
    }

    private Map<String, Integer> getConcreteValues(final Term pathCondition,
            final Services services) throws ModelGeneratorException {

        try {
            /*
             * Simplify the path condition. If the simplified path condition is
             * null, this means that it does not contain any primitive values.
             * There is hence nothing useful we can do with it, and we just
             * return it as null.
             */
            Term simplifiedPathCondition = ModelGenerationTools.simplifyTerm(pathCondition);

            simplifiedPathCondition = NormalizeArithmeticComparatorsTransformer.getInstance(
                    services).transform(simplifiedPathCondition);

            if (simplifiedPathCondition == null) {
                return null;
            } else {
                return keYStone.solveConstraint(simplifiedPathCondition);
            }

        } catch (final TermTransformerException e) {
            throw new ModelGeneratorException(e.getMessage());
        } catch (final KeYStoneException e) {
            throw new ModelGeneratorException(e.getMessage());
        }
    }

    private void instantiateModel(final Model model,
            final Map<String, Integer> concreteValues) {

        for (final String variableName : concreteValues.keySet()) {

            final ModelVariable variable = model.getVariable(variableName);

            if (variable != null) {
                variable.setValue(concreteValues.get(variableName));
            }
        }
    }
}