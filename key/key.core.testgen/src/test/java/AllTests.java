import org.junit.runner.RunWith;
import org.junit.runners.Suite;

/**
 * @author Alexander Weigl
 * @version 1 (20.07.19)
 */
@Suite.SuiteClasses({
        de.uka.ilkd.key.testcase.smt.testgen.TestTestgen.class,
        de.uka.ilkd.key.testcase.smt.ce.TestCE.class
})
@RunWith(Suite.class)
public class AllTests {
}
