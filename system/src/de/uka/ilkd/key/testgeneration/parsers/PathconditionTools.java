package de.uka.ilkd.key.testgeneration.parsers;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.testgeneration.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.model.implementation.Model;
import de.uka.ilkd.key.testgeneration.model.implementation.ModelMediator;

/**
 * Provides various methods for processing the pathconditions for
 * {@link IExecutionNode} instances.
 * 
 * @author christopher
 */
public class PathconditionTools {

    private static final TermSimplificationTransformer termSimplificationTransformer = new TermSimplificationTransformer();

    private static final PathToTermParser pathToTermParser = new PathToTermParser();

    /**
     * Allow only static access
     */
    private PathconditionTools() {

    }

    /**
     * Given an initial {@link Term}, constructs a simpler Term which
     * "localizes" all occurences of primitive datatypes, by transforming the
     * instances of {@link SortDependingFunction} which contain them.
     * <p>
     * As an example of how this works, consider the case where we have an
     * instace of some class <code>Base</code> named "base", which as a field
     * has an instance of some other class <code>Inner</code> named "inner",
     * which in turn has a local instance of an <code>integer </code> named
     * "localInt. Normally, simply transforming such a construct to an SMT-LIB
     * formula would result in a needlesly complex expression and model, which
     * is a waste of both resources and time invested in developing additional
     * parsers to understand it.
     * <p>
     * What we do instead is to simply transform the construct into a local
     * variable of our base class, giving it a name corresponding to its nesting
     * order. In our case, such a name migh be "base$nested$localInt". When all
     * variables have been processed like this, we end up with a greatly
     * simplified term which can easily be expressed as an SMT-LIB construct.
     * <p>
     * This process will also remove all implied properties of internal objects,
     * such as not-null requirements, since these are not needed in the
     * simplified formula, and would only further pollute the SMT-LIB
     * expression. Further, it will simplify the formula by removing unnecessary
     * conjuntions.
     * 
     * @param term
     *            the term to process
     * @return the simplified term
     * @throws TermTransformerException
     * @throws ModelGeneratorException
     */
    public static Term simplifyTerm(Term targetNodeCondition)
            throws TermTransformerException {

        return termSimplificationTransformer.simplifyTerm(targetNodeCondition);
    }

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
     */
    public static Model createModel(Term pathCondition, Services services,
            ModelMediator mediator) {

        return pathToTermParser.createModel(pathCondition, services, mediator);
    }

}