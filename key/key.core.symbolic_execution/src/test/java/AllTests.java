import org.junit.runner.RunWith;
import org.junit.runners.Suite;

/**
 * @author Alexander Weigl
 * @version 1 (20.07.19)
 */
@Suite.SuiteClasses({
        de.uka.ilkd.key.symbolic_execution.testcase.TestSymbolicExecutionTreeBuilder.class,
        de.uka.ilkd.key.symbolic_execution.testcase.TestSymbolicLayoutWriterAndReader.class,
        de.uka.ilkd.key.symbolic_execution.testcase.TestSymbolicLayoutExtractor.class,
        de.uka.ilkd.key.symbolic_execution.testcase.TestConditionalVariables.class,
        de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestKeYWatchpointGlobalVariablesOnSatisfiable.class,
        de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestMethodBreakpointWithHitCount.class,
        de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestExceptionBreakpointStopConditionWithSubclasses.class,
        de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestStepReturnSymbolicExecutionTreeNodesStopCondition.class,
        de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestKeYWatchpointMethodsOnSatisfiable.class,
        de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestLineBreakpointStopConditionSimpleWithHitCount.class,
        de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestMethodBreakpointWithConditions.class,
        de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestStepOverSymbolicExecutionTreeNodesStopCondition.class,
        de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestLineBreakpointStopConditionSimpleWithLoopInvariant.class,
        de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestExceptionBreakpointStopConditionCaughtOrUncaught.class,
        de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestJavaWatchpointStopConditionWithHitCount.class,
        de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestLineBreakpointStopConditionSimpleWithConditions.class,
        de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestSymbolicExecutionStrategy.class,
        de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestExceptionBreakpointStopConditionWithHitCount.class,
        de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestKeYWatchpointGlobalVariablesOnTrueWithHitCount.class,
        de.uka.ilkd.key.symbolic_execution.testcase.TestExecutionNodeWriterAndReader.class,
        de.uka.ilkd.key.symbolic_execution.testcase.TestExecutionVariableExtractor.class,
        de.uka.ilkd.key.symbolic_execution.testcase.TestParallelSiteProofs.class,
        de.uka.ilkd.key.symbolic_execution.testcase.util.TestEqualsHashCodeResetter.class,
        de.uka.ilkd.key.symbolic_execution.testcase.util.TestSideProofStore.class,
        de.uka.ilkd.key.symbolic_execution.testcase.util.TestDefaultEntry.class,
        de.uka.ilkd.key.symbolic_execution.testcase.util.TestSymbolicExecutionUtil.class,
        de.uka.ilkd.key.symbolic_execution.testcase.TestTruthValueValue.class,
        de.uka.ilkd.key.symbolic_execution.testcase.TestExecutionNodePreorderIterator.class,
        de.uka.ilkd.key.symbolic_execution.testcase.po.TestProgramMethodPO.class,
        de.uka.ilkd.key.symbolic_execution.testcase.po.TestFunctionalOperationContractPO.class,
        de.uka.ilkd.key.symbolic_execution.testcase.po.TestProgramMethodSubsetPO.class,
        de.uka.ilkd.key.symbolic_execution.testcase.slicing.TestThinBackwardSlicer.class,
        de.uka.ilkd.key.symbolic_execution.testcase.TestTruthValueEvaluationUtil.class
})
@RunWith(Suite.class)
public class AllTests {
}
