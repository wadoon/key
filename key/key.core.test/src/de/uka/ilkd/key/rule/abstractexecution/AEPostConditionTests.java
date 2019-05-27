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

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.merge.MergeRuleTests;
import junit.framework.TestCase;

/**
 * @author Dominic Steinhoefel
 *
 */
public class AEPostConditionTests extends TestCase {
    private static final String TEST_RESOURCES_DIR_PREFIX = "resources/testcase/abstractexecution/";

    @Test
    public void testPostConditionExampleStep0() {
        final Proof proof = MergeRuleTests.loadProof(TEST_RESOURCES_DIR_PREFIX,
                "postcondition/step0.key");
        MergeRuleTests.startAutomaticStrategy(proof);

        assertTrue(proof.closed());
    }

    @Test
    public void testPostConditionExampleStep1() {
        final Proof proof = MergeRuleTests.loadProof(TEST_RESOURCES_DIR_PREFIX,
                "postcondition/step1.key");
        MergeRuleTests.startAutomaticStrategy(proof);

        assertTrue(proof.closed());
    }

    @Test
    public void testPostConditionExampleStep2() {
        final Proof proof = MergeRuleTests.loadProof(TEST_RESOURCES_DIR_PREFIX,
                "postcondition/step2.key");
        MergeRuleTests.startAutomaticStrategy(proof);

        assertTrue(proof.closed());
    }

    @Test
    public void testDutchFlag0() {
        dutchFlag(0);
    }

    @Test
    public void testDutchFlag1() {
        dutchFlag(1);
    }

    @Test
    public void testDutchFlag2() {
        dutchFlag(2);
    }

    @Test
    public void testDutchFlag3() {
        dutchFlag(3);
    }

    private void dutchFlag(int i) {
        final Proof proof = MergeRuleTests.loadProof(TEST_RESOURCES_DIR_PREFIX,
                "arrays/step" + i + ".key");
        MergeRuleTests.startAutomaticStrategy(proof);

        assertTrue(proof.closed());
    }
}
