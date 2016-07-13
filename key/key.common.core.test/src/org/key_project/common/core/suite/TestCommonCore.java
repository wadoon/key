// This file is part of KeY - Integrated Deductive Software Design

//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2016 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package org.key_project.common.core.suite;

import junit.framework.TestCase;
import junit.framework.TestResult;
import junit.framework.TestSuite;

/**
 * The test suite for common.core. This should be extended by more tests when
 * the refactoring proceeds.
 *
 * @author Dominic Scheurer
 */
@SuppressWarnings("unchecked")
public class TestCommonCore extends TestSuite {

    static Class<? extends TestCase>[] utilityTests = new Class[] {
    };

    static Class<? extends TestCase>[] logicModelTests = new Class[] {
    };

    static Class<? extends TestCase>[] parserTests = new Class[] {
            org.key_project.common.core.parser.TestDeclParser.class
    };

    static Class<? extends TestCase>[] ruleTests = new Class[] {
    };

    static Class<? extends TestCase>[] proofConstructionTests = new Class[] {
    };

    static Class<? extends TestCase>[] speclangTests = new Class[] {
    };

    static Class<? extends TestCase>[] smtTests = new Class[] {
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
        // suite.addTest(createSuite(utilityTests, "Testing KeY specific
        // Utilities"));
        // suite.addTest(createSuite(logicModelTests, "Testing Logic Engine"));
        suite.addTest(createSuite(parserTests, "Testing Parsers"));
        // suite.addTest(createSuite(ruleTests, "Testing Rule Engine"));
        // suite.addTest(createSuite(proofConstructionTests, "Testing Proof
        // Construction"));
        // suite.addTest(createSuite(speclangTests, "Testing JML frontend"));
        // suite.addTest(createSuite(smtTests, "Testing SMT backend"));

        return suite;
    }

    public TestCommonCore(String name) {
        super(name);
    }
}