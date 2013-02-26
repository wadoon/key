package de.uka.ilkd.key.testgeneration.core.model.tools;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.testgeneration.core.model.implementation.Model;
import de.uka.ilkd.key.testgeneration.core.model.implementation.ModelMediator;
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.NegationNormalFormTransformer;
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.RemoveIfThenElseTransformer;
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.TermTransformerException;

class TermToModelConverter {

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
     */
    public static Model createModel(Term term, Services services,
            ModelMediator mediator) throws TermTransformerException {

        Model model = new Model();

        /*
         * Remove if-then-else statements from the pathcondition
         */
        term = new RemoveIfThenElseTransformer().transform(term);

        /*
         * Construct the initial Model, containing representation of all the
         * variables and values found in the Term. Done postorder to eliminate
         * buffering penalties in the Model.
         */
        TermToModelVisitor modelVisitor = new TermToModelVisitor(model,
                services, mediator);
        term.execPostOrder(modelVisitor);

        /*
         * Distribute negations and remove conjunctions
         */
        term = new NegationNormalFormTransformer().transform(term);
        term = new EliminateConjunctionsTransformer().transform(term);

        /*
         * Setup all reference relationships expressed in the Term. Done
         * preorder to correctly handle non-assigning operations, such as
         * not-equals.
         */
        ResolveVariableAssignmentVisitor referenceVisitor = new ResolveVariableAssignmentVisitor(
                model);
        term.execPreOrder(referenceVisitor);

        return modelVisitor.getModel();
    }
}