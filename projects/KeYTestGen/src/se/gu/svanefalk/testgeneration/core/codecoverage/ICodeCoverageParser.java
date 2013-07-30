package se.gu.svanefalk.testgeneration.core.codecoverage;

import java.util.List;

import se.gu.svanefalk.testgeneration.core.codecoverage.implementation.BranchCoverageParser;
import se.gu.svanefalk.testgeneration.core.codecoverage.implementation.ConditionCoverageParser;
import se.gu.svanefalk.testgeneration.core.codecoverage.implementation.DecisionCoverageParser;
import se.gu.svanefalk.testgeneration.core.codecoverage.implementation.ModifiedConditionDecisionCoverageParser;
import se.gu.svanefalk.testgeneration.core.codecoverage.implementation.PathCoverageParser;
import se.gu.svanefalk.testgeneration.core.codecoverage.implementation.StatementCoverageParser;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStart;

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
public interface ICodeCoverageParser {

    static ICodeCoverageParser branchCoverageParser = new BranchCoverageParser();
    static ICodeCoverageParser conditionCoverageParser = new ConditionCoverageParser();
    static ICodeCoverageParser decisionCoverageParser = new DecisionCoverageParser();
    static ICodeCoverageParser modifiedConditionDecisionCoverageParser = new ModifiedConditionDecisionCoverageParser();
    static ICodeCoverageParser pathCoverageParser = new PathCoverageParser();
    static ICodeCoverageParser statementCoverageParser = new StatementCoverageParser();

    public List<IExecutionNode> retrieveNodes(IExecutionStart root);
}
