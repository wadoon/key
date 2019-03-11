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

import org.junit.Test;

import de.uka.ilkd.key.proof.Proof;
import junit.framework.TestCase;

/**
 * Test suite for the abstract execution taclets.
 *
 * @author Dominic Steinhoefel
 */
public class AbstractExecutionTests extends TestCase {
    private static final String TEST_RESOURCES_DIR_PREFIX = "resources/testcase/abstractexecution/";

    @Test
    public void test() {
        final Proof proof = loadProof(TEST_RESOURCES_DIR_PREFIX,
                "correct-refactoring-ite-pullout-prefix-with-notassgn-spec/pulloutITEPrefixRef.key");
        startAutomaticStrategy(proof);

        assertTrue(proof.closed());
    }

    @Test
    public void testFieldExtraction() {
        final String heapExpr = "store(store(heap, self, TestAEHeap::$field1, Z(7(1(#)))), self, TestAEHeap::$field2, Z(2(4(#))))";

    }
}