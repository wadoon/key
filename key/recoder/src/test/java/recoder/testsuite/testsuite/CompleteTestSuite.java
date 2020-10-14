/*
 * Created on 18.04.2005
 *
 * This file is part of the RECODER library and protected by the LGPL.
 */
package recoder.testsuite.testsuite;

import java.io.IOException;
import java.util.Enumeration;

import junit.framework.TestFailure;
import junit.framework.TestResult;
import junit.framework.TestSuite;
import recoder.testsuite.testsuite.basic.BasicTestsSuite;
import recoder.testsuite.testsuite.completeCoverage.CompleteCoverage;
import recoder.testsuite.testsuite.fixedbugs.FixedBugs;
import recoder.testsuite.testsuite.java5test.Java5Test;
import recoder.testsuite.testsuite.newFeatures.NameInfoPatternMatcher;
import recoder.testsuite.testsuite.newFeatures.SmallFeatures;
import recoder.testsuite.testsuite.semantics.ASTChecks;
import recoder.testsuite.testsuite.semantics.SemanticsChecks;
import recoder.testsuite.testsuite.transformation.TransformationTests;

/**
 * @author gutzmann
 *
 */
public class CompleteTestSuite extends TestSuite {

    /**
     * @throws InstantiationException
     * @throws IllegalAccessException
     * @throws ClassNotFoundException
     * @throws IOException
     * 
     */
    public CompleteTestSuite() throws IOException, ClassNotFoundException, IllegalAccessException, InstantiationException {
        super();
        addTest(BasicTestsSuite.suite()); 
        addTestSuite(FixedBugs.class);
        addTestSuite(TransformationTests.class);
        addTestSuite(Java5Test.class);
        addTest(CompleteCoverage.suite());
        addTestSuite(NameInfoPatternMatcher.class);
        addTestSuite(SmallFeatures.class);
        addTestSuite(ASTChecks.class);
        addTestSuite(SemanticsChecks.class);
    }

    public static TestSuite suite() throws IOException, ClassNotFoundException, IllegalAccessException, InstantiationException {
        return new CompleteTestSuite();
    }

    public static void main(String args[]) {
        try {
            TestResult tr = new TestResult();
            new CompleteTestSuite().run(tr);
            System.out.println("Testsuite result: " + tr.failureCount() + " failures, " + tr.errorCount() + " errors " + tr.runCount() + " total runs");
            Enumeration<?> errors = tr.errors();
            while (errors.hasMoreElements()) {
                System.out.println("ERROR");
                System.out.println("=====");
                Throwable error = (Throwable)errors.nextElement();
                error.printStackTrace(System.out);
                System.out.println("\n");
            }
            Enumeration<?> failures = tr.failures();
            while (failures.hasMoreElements()) {
                System.out.println("FAILURE");
                System.out.println("=======");
                TestFailure failure = (TestFailure)failures.nextElement();
                failure.thrownException().printStackTrace(System.out);
                System.out.println("\n");
            }
        } catch (Exception e) {
            System.err.println("Testsuite failed to exception: " + e.getMessage());
            e.printStackTrace();
        }
    }
}
