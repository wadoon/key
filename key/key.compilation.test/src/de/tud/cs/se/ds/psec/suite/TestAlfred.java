package de.tud.cs.se.ds.psec.suite;

import junit.framework.TestCase;
import junit.framework.TestResult;
import junit.framework.TestSuite;

/**
 * Test suite for key.compilation.
 *
 * @author Dominic Scheurer
 */
public class TestAlfred extends TestSuite {

    @SuppressWarnings("unchecked")
    static Class<? extends TestCase>[] parserTests = new Class[] {
            de.tud.cs.se.ds.psec.parser.ParserTest.class,
    };

    @SuppressWarnings("unchecked")
    static Class<? extends TestCase>[] compilerTests = new Class[] {
            de.tud.cs.se.ds.psec.compiler.SimpleCompilerFunctionalTests.class,
            de.tud.cs.se.ds.psec.compiler.MethodCallFunctionalTests.class,
    };

    public static TestSuite createSuite(Class<? extends TestCase>[] testClasses, final String msg) {
        TestSuite suite = new TestSuite() {
            @Override
            public void run(TestResult result) {
                System.out.print("[" + msg + "]: ");
                super.run(result);
                System.out.println();
            }
        };

        for (int i = 0; i < testClasses.length; i++) {
            suite.addTest(new TestSuite(testClasses[i]));
        }

        return suite;
    }

    public static junit.framework.Test suite() {
        TestSuite suite = new TestSuite();
        suite.addTest(createSuite(parserTests, "Testing Parsers"));
        suite.addTest(createSuite(compilerTests, "Testing Compiler"));

        return suite;
    }
    
    public TestAlfred(String name) {
        super(name);
    }

}
