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

import java.io.File;

import org.junit.Test;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.merge.MergeRuleTests;
import de.uka.ilkd.key.util.HelperClassForTests;
import junit.framework.TestCase;

/**
 * @author Dominic Steinhoefel
 *
 */
public class AEHeapTests extends TestCase {
    private static final File TEST_RESOURCES_DIR_PREFIX = new File(HelperClassForTests.TESTCASE_DIRECTORY, "abstractexecution/");

    @Test
    public void testRunCloseableExample() {
        final Proof proof = MergeRuleTests.loadProof(TEST_RESOURCES_DIR_PREFIX,
                "heap/closable.key");
        MergeRuleTests.startAutomaticStrategy(proof);

        assertTrue(proof.closed());
    }

    @Test
    public void testRunUncloseableExample() {
        final Proof proof = MergeRuleTests.loadProof(TEST_RESOURCES_DIR_PREFIX,
                "heap/unclosable.key");
        MergeRuleTests.startAutomaticStrategy(proof);

        assertFalse(proof.closed());
        assertEquals(1, proof.openGoals().size());
    }

    @Test
    public void testIneffectiveArrayAssignment() {
        final Proof proof = MergeRuleTests.loadProof(TEST_RESOURCES_DIR_PREFIX,
                "arrays/basicTests/throwAwayAssignmentToSingleField.key");
        MergeRuleTests.startAutomaticStrategy(proof);

        assertTrue(proof.closed());
    }

    @Test
    public void testEffectiveArrayAssignment() {
        final Proof proof = MergeRuleTests.loadProof(TEST_RESOURCES_DIR_PREFIX,
                "arrays/basicTests/cannotThrowAwayAssignmentToSingleField.key");
        MergeRuleTests.startAutomaticStrategy(proof);

        assertFalse(proof.closed());
        assertEquals(2, proof.openGoals().size());
    }

    @Test
    public void testDutchFlag0() {
        dutchFlag("0");
    }

    @Test
    public void testDutchFlag1() {
        dutchFlag("1");
    }

    @Test
    public void testDutchFlag1a() {
        dutchFlag("1a");
    }

    @Test
    public void testDutchFlag2() {
        dutchFlag("2");
    }

    @Test
    public void testDutchFlag3() {
        dutchFlag("3");
    }

    private void dutchFlag(String i) {
        final Proof proof = MergeRuleTests.loadProof(TEST_RESOURCES_DIR_PREFIX,
                String.format("arrays/dutchFlag/step%s.key", i));
        MergeRuleTests.startAutomaticStrategy(proof);

        assertTrue(proof.closed());
    }
}
