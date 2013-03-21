package se.gu.svanefalk.testgeneration.core.codecoverage.implementation;

import java.util.List;

import se.gu.svanefalk.testgeneration.core.codecoverage.ICodeCoverageParser;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;

/**
 * Instances of this interface are used in order to parse a tree consisting of
 * {@link IExecutionNode} instances, and return a subset of those nodes based on
 * some criteria.
 * <p>
 * The common use of such parsers in KeYTestGen is to guarantee a certain degree
 * of code coverage for the code being tested. The returned set of nodes will in
 * this case form a basis for a test suite which will satisfy the targeted code
 * coverage criteria.
 * 
 * @author christopher
 */
public class ModifiedConditionDecisionCoverageParser implements
        ICodeCoverageParser {

    @Override
    public List<IExecutionNode> retrieveNodes(final IExecutionStartNode root) {

        throw new UnsupportedOperationException("Not implemented yet");
    }
}
