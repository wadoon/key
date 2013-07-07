package se.gu.svanefalk.testgeneration.core.model.implementation;

import se.gu.svanefalk.testgeneration.core.model.tools.EliminateConjunctionsTransformer;
import se.gu.svanefalk.testgeneration.util.transformers.NegationNormalFormTransformer;
import se.gu.svanefalk.testgeneration.util.transformers.RemoveIfThenElseTransformer;
import se.gu.svanefalk.testgeneration.util.transformers.RemoveImplicationsTransformer;
import se.gu.svanefalk.testgeneration.util.transformers.TermTransformerException;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

public class ModelBuilder {

    /**
     * Creates a skeletal {@link Model} instance from a {@link Term}. The Term
     * will be parsed, and all representations of program variables (along with
     * their relationships to one another) will be used to construct a
     * "skeletal" Model instance (i.e. no concrete primitive values).
     * 
     * @param term
     *            the Term to process
     * @param services
     *            {@link Services} associated with the Term
     * @param mediator
     *            session mediator
     * @return the Model instance built from the Term
     * @throws TermTransformerException
     * @throws ProofInputException
     */
    public Model createModel(IExecutionNode node, Term pathCondition)
            throws TermTransformerException, ProofInputException {

        final Model model = Model.constructModel();

        /*
         * Construct the initial Model, containing representation of all the
         * variables and values found in the Term. Done postorder to eliminate
         * buffering penalties in the Model.
         */
        ModelBuilderVisitor visitor = new ModelBuilderVisitor(model, node);
        pathCondition.execPostOrder(visitor);

        /*
         * Distribute negations and remove conjunctions
         */
        pathCondition = NegationNormalFormTransformer.getInstance().transform(
                pathCondition);

        pathCondition = EliminateConjunctionsTransformer.getInstance().transform(
                pathCondition);

        /*
         * Setup all reference relationships expressed in the Term. Done
         * preorder to correctly handle non-assigning operations, such as
         * not-equals.
         */
        final ResolveAssignmentsVisitor referenceVisitor = new ResolveAssignmentsVisitor(
                model);
        pathCondition.execPreOrder(referenceVisitor);

        return visitor.getModel();
    }
}