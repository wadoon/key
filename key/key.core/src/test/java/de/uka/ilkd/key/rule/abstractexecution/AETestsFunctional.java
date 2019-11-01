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
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import org.junit.Test;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.GenericTermReplacer;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.merge.MergeRuleTests;
import de.uka.ilkd.key.util.HelperClassForTests;
import junit.framework.TestCase;

/**
 * @author Dominic Steinhoefel
 */
public class AETestsFunctional extends TestCase {
    private static final File TEST_RESOURCES_DIR_PREFIX = new File(
            HelperClassForTests.TESTCASE_DIRECTORY, "abstractexecution/functional/");

    @Test
    public void testIrrelevantAPS() {
        final Proof proof = MergeRuleTests.loadProof(TEST_RESOURCES_DIR_PREFIX, "irrelevantAS.key");
        MergeRuleTests.startAutomaticStrategy(proof);

        assertTrue(proof.closed());
    }

    @Test
    public void testRelevantAPS() {
        final Proof proof = MergeRuleTests.loadProof(TEST_RESOURCES_DIR_PREFIX, "relevantAS.key");
        MergeRuleTests.startAutomaticStrategy(proof);

        assertFalse(proof.closed());
        assertEquals(1, proof.openGoals().size());

        final String expectedFormula = "{x:=1 || U_P(frameP:={x:=1}value(footprintP))}x = 1";

        assertTrue(semisequentContainsFormula(expectedFormula,
                proof.openGoals().head().sequent().succedent(), proof.getServices()));
    }

    private boolean semisequentContainsFormula(final String formulaString,
            final Semisequent semisequent, final Services services) {
        boolean containsExpectedSuccFor = false;

        for (final Term formula : StreamSupport.stream(semisequent.spliterator(), false)
                .map(SequentFormula::formula).collect(Collectors.toList())) {
            if (LogicPrinter.quickPrintTerm(stripTermLabels(formula, services), services).trim()
                    .equals(formulaString)) {
                containsExpectedSuccFor = true;
                break;
            }
        }

        return containsExpectedSuccFor;
    }

    private static Term stripTermLabels(Term t, Services services) {
        return GenericTermReplacer.replace(t, t1 -> t1.hasLabels(), t1 -> services.getTermFactory()
                .createTerm(t1.op(), t1.subs(), t1.boundVars(), t1.javaBlock(), null), services);
    }
}
