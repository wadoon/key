// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.rule.abstractexecution;

import org.junit.Test;

import de.uka.ilkd.key.rule.merge.MergeRuleTests;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import junit.framework.TestCase;

/**
 * @author Dominic Steinhoefel
 *
 */
public class AETypeCheckerTests extends TestCase {
    private static final String TEST_RESOURCES_DIR_PREFIX = //
            "resources/testcase/abstractexecution/typechecker/";

    @Test
    public void testIncorrectAccessible() {
        final String expectedMsg = "The following locations are specified to be "
                + "accessible by abstract program Q, but are not declared: localsP";

        try {
            MergeRuleTests.loadProof(TEST_RESOURCES_DIR_PREFIX,
                    "IncorrectAccessible/extractMethodRefactoring.key", false);
            fail("This proof should not load.");
        }
        catch (Throwable e) {
            assertEquals(SLTranslationException.class, e.getCause().getClass());
            assertEquals(expectedMsg, e.getMessage());
        }
    }
}