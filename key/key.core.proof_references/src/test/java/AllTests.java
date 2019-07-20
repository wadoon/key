import org.junit.runner.RunWith;
import org.junit.runners.Suite;

/**
 * @author Alexander Weigl
 * @version 1 (20.07.19)
 */
@Suite.SuiteClasses({
        de.uka.ilkd.key.proof_references.testcase.analyst.TestContractProofReferencesAnalyst.class,
        de.uka.ilkd.key.proof_references.testcase.analyst.TestProgramVariableReferencesAnalyst.class,
        de.uka.ilkd.key.proof_references.testcase.analyst.TestMethodCallProofReferencesAnalyst.class,
        de.uka.ilkd.key.proof_references.testcase.analyst.TestMethodBodyExpandProofReferencesAnalyst.class,
        de.uka.ilkd.key.proof_references.testcase.analyst.TestClassAxiomAndInvariantProofReferencesAnalyst.class,
        de.uka.ilkd.key.proof_references.testcase.TestKeYTypeUtil.class,
        de.uka.ilkd.key.proof_references.testcase.TestProofReferenceUtil.class
})
@RunWith(Suite.class)
public class AllTests {
}
