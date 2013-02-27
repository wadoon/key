package de.uka.ilkd.key.testgeneration.core.model.implementation;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.testgeneration.StringConstants;
import de.uka.ilkd.key.testgeneration.core.model.tools.EliminateConjunctionsTransformer;
import de.uka.ilkd.key.testgeneration.util.parsers.TermParserException;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.NegationNormalFormTransformer;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.RemoveIfThenElseTransformer;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.TermTransformerException;
import de.uka.ilkd.key.testgeneration.util.parsers.visitors.KeYTestGenTermVisitor;

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
     * @throws ProofInputException
     */
    public static Model createModel(IExecutionNode node)
            throws TermTransformerException, ProofInputException {

        Term pathCondition = node.getPathCondition();

        Model model = new Model();

        /*
         * Remove if-then-else statements from the pathcondition
         */
        pathCondition = new RemoveIfThenElseTransformer()
                .transform(pathCondition);

        /*
         * Construct the initial Model, containing representation of all the
         * variables and values found in the Term. Done postorder to eliminate
         * buffering penalties in the Model.
         */
        TermToModelVisitor modelVisitor = new TermToModelVisitor(model, node);
        pathCondition.execPostOrder(modelVisitor);

        /*
         * Distribute negations and remove conjunctions
         */
        pathCondition = new NegationNormalFormTransformer()
                .transform(pathCondition);
        pathCondition = new EliminateConjunctionsTransformer()
                .transform(pathCondition);

        /*
         * Setup all reference relationships expressed in the Term. Done
         * preorder to correctly handle non-assigning operations, such as
         * not-equals.
         */
        ResolveAssignmentsVisitor referenceVisitor = new ResolveAssignmentsVisitor(
                model);
        pathCondition.execPreOrder(referenceVisitor);

        return modelVisitor.getModel();
    }
}