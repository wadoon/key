import org.junit.runner.RunWith;
import org.junit.runners.Suite;

/**
 * @author Alexander Weigl
 * @version 1 (20.07.19)
 */
@Suite.SuiteClasses({
        org.key_project.util.collection.TestImmutables.class,
        org.key_project.util.testcase.collection.TestMapAsListFromIntegerToString.class,
        org.key_project.util.testcase.collection.TestLeftistHeapOfInteger.class,
        org.key_project.util.testcase.collection.TestSLListOfString.class,
        org.key_project.util.testcase.collection.TestSetAsListOfString.class,
        org.key_project.util.testcase.java.NumberUtilTest.class,
        org.key_project.util.testcase.java.XMLUtilTest.class,
        org.key_project.util.testcase.java.ArrayUtilTest.class,
        org.key_project.util.testcase.java.CollectionUtilTest.class,
        org.key_project.util.testcase.java.IOUtilTest.class,
        org.key_project.util.testcase.java.StringUtilTest.class,
        org.key_project.util.testcase.java.IntegerUtilTest.class,
        org.key_project.util.testcase.java.ObjectUtilTest.class,
        org.key_project.util.testcase.bitops.TestFixedLengthBitSet.class
})
@RunWith(Suite.class)
public class AllTests {
}
