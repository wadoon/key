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

package de.tud.cs.se.ds.specstr.analyzer;

import static de.tud.cs.se.ds.specstr.analyzer.Analyzer.FactType.POST_COND_FACT;

import org.junit.Test;

import de.tud.cs.se.ds.specstr.analyzer.Analyzer.AnalyzerResult;

/**
 * TODO
 *
 * @author Dominic Steinhoefel
 */
public class LoopFreeTest extends AbstractAnalyzerTest {

    @Test
    public void testAbsWeakPost() {
        final AnalyzerResult result = analyzeMethod( //
                "loopFree/SimpleMath.java", //
                "SimpleMath::abs(I)I");

        assertEquals(2, result.getUncoveredFactsOfType(POST_COND_FACT).size());
        assertEquals(2, result.numFacts());
    }

    @Test
    public void testAbsStronger1() {
        // Here, the post condition is "\result >= 0".
        // This is a case where we could apply the generalization...
        final AnalyzerResult result = analyzeMethod( //
                "loopFree/SimpleMath.java", //
                "SimpleMath::abs_stronger_1(I)I");

        assertEquals(2, result.getAbstractlyCoveredFactsOfType(POST_COND_FACT).size());
        assertEquals(2, result.numFacts());
    }

    @Test
    public void testAbsStronger2() {
        final AnalyzerResult result = analyzeMethod( //
                "loopFree/SimpleMath.java", //
                "SimpleMath::abs_stronger_2(I)I");

        assertEquals(1, result.getCoveredFactsOfType(POST_COND_FACT).size());
        assertEquals(1, result.getUncoveredFactsOfType(POST_COND_FACT).size());
        assertEquals(2, result.numFacts());
    }

    @Test
    public void testAbsStronger3() {
        final AnalyzerResult result = analyzeMethod( //
                "loopFree/SimpleMath.java", //
                "SimpleMath::abs_stronger_3(I)I");

        assertEquals(1, result.getCoveredFactsOfType(POST_COND_FACT).size());
        assertEquals(1, result.getUncoveredFactsOfType(POST_COND_FACT).size());
        assertEquals(2, result.numFacts());
    }

    @Test
    public void testAbsStrongest() {
        final AnalyzerResult result = analyzeMethod( //
                "loopFree/SimpleMath.java", //
                "SimpleMath::abs_strongest(I)I");

        assertEquals(0, result.numUncoveredFacts());
    }

}
