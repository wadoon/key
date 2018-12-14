// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.abstractexecution;

import static de.uka.ilkd.key.rule.merge.MergeRuleTests.loadProof;
import static de.uka.ilkd.key.rule.merge.MergeRuleTests.startAutomaticStrategy;

import java.util.Iterator;

import org.junit.Test;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.Taclet;
import junit.framework.TestCase;

/**
 * Test suite for the abstract execution taclets.
 *
 * @author Dominic Steinhoefel
 */
public class AbstractExecutionTests extends TestCase {
    private static final String TEST_RESOURCES_DIR_PREFIX =
            "resources/testcase/abstractexecution/";

    @Test
    public void testProofCorrectIfThenElseCommonPostfixRefactoring() {
        final Proof proof = loadProof(TEST_RESOURCES_DIR_PREFIX,
                "correct-refactoring-ite-pullout-postfix.key");
        startAutomaticStrategy(proof);

        assertTrue(proof.closed());

        final Iterator<Node> it = proof.root().subtreeIterator();
        int abstractExecAppsCnt = 0;
        while (it.hasNext()) {
            final Node nextNode = it.next();
            if (nextNode.getAppliedRuleApp() == null) {
                continue;
            }

            final Rule rule = nextNode.getAppliedRuleApp().rule();
            if (rule instanceof FindTaclet
                    && ((Taclet) rule).getRuleSets().stream().anyMatch(rs -> rs
                            .name().toString().equals("abstractExecution"))) {
                abstractExecAppsCnt++;
            }
        }

        final int expectedNumAEApps = 16;
        assertEquals(
                String.format("There should be %d abstract execution apps.",
                        expectedNumAEApps),
                expectedNumAEApps, abstractExecAppsCnt);
    }

    @Test
    public void testProofIncorrectIfThenElseCommonPrefixRefactoring() {
        final Proof proof = loadProof(TEST_RESOURCES_DIR_PREFIX,
                "incorrect-refactoring-ite-pullout-prefix.key");
        startAutomaticStrategy(proof);

        assertFalse(proof.closed());
        assertEquals(4, proof.openGoals().size());

        final Iterator<Node> it = proof.root().subtreeIterator();
        int abstractExecAppsCnt = 0;
        while (it.hasNext()) {
            final Node nextNode = it.next();
            if (nextNode.getAppliedRuleApp() == null) {
                continue;
            }

            final Rule rule = nextNode.getAppliedRuleApp().rule();
            if (rule instanceof FindTaclet
                    && ((Taclet) rule).getRuleSets().stream().anyMatch(rs -> rs
                            .name().toString().equals("abstractExecution"))) {
                abstractExecAppsCnt++;
            }
        }

        final int expectedNumAEApps = 18;
        assertEquals(
                String.format("There should be %d abstract execution apps.",
                        expectedNumAEApps),
                expectedNumAEApps, abstractExecAppsCnt);

        /*
         * TODO (DS, 2018-12-14): Maybe check that this proof can be closed if
         * we substitute all the {U_sk_0} by SKIP...
         */
    }
}
