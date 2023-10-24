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

import static de.tud.cs.se.ds.specstr.analyzer.Analyzer.FactType.*;

import java.util.List;

import org.junit.Test;

import de.tud.cs.se.ds.specstr.analyzer.Analyzer.AnalyzerResult;
import de.tud.cs.se.ds.specstr.analyzer.Analyzer.Fact;

/**
 * A test suite based on multiple specifications for a simple "find-in-array"
 * method with one loop.
 *
 * @author Dominic Steinhoefel
 */
public class FindMethodsTest extends AbstractAnalyzerTest {

    @Test
    public void testFindStrongestPost() {
        final AnalyzerResult result = analyzeMethod(
            "findMethods/FindMethods.java",
            "FindMethods::find_strongest_post([II)I");

        assertEquals(100d, result.coveredStrength(), 0d);
        assertEquals(100d, result.strength(), 0d);
        
        assertEquals(0, result.unclosedLoopInvPreservedGoals());
        assertEquals(0, result.problematicExceptions().size());

        assertEquals(0, result.numUncoveredFacts());
        assertEquals(0, result.numAbstractlyCoveredFacts());
    }

    @Test
    public void testFindStrongestInv() {
        final AnalyzerResult result = analyzeMethod(
            "findMethods/FindMethods.java",
            "FindMethods::find_strongest_inv([II)I");

        assertEquals(87.5d, result.coveredStrength(), 0d);
        assertEquals(93.75d, result.strength(), 0d);
        
        assertEquals(0, result.unclosedLoopInvPreservedGoals());
        assertEquals(0, result.problematicExceptions().size());

        assertEquals(0, result.numUncoveredFacts());
        assertEquals(1, result.numAbstractlyCoveredFacts());

        final List<Fact> abstrPostCondFacts = result
                .getAbstractlyCoveredFactsOfType(POST_COND_FACT);

        assertEquals("result = iLastRun_0",
            abstrPostCondFacts.get(0).getDescr());
        assertContains("!result_1_0 = -1",
            abstrPostCondFacts.get(0).getPathCond());
    }

    @Test
    public void testFindStrongerPost() {
        final AnalyzerResult result = analyzeMethod(
            "findMethods/FindMethods.java",
            "FindMethods::find_stronger_post([II)I");

        assertEquals(50d, result.coveredStrength(), 0d);
        assertEquals(58.33d, result.strength(), .01d);
        
        assertEquals(0, result.unclosedLoopInvPreservedGoals());
        assertEquals(0, result.problematicExceptions().size());

        final List<Fact> loopBodyFacts = result
                .getUncoveredFactsOfType(LOOP_BODY_FACT);

        assertEquals(2, loopBodyFacts.size());
        assertEquals(0, result.getUncoveredFactsOfType(POST_COND_FACT).size());

        assertEquals(2, result.numUncoveredFacts());

        loopBodyFacts.forEach(f -> {
            assertEquals("i = 1 + i_0", f.getDescr());
        });

        assertContains("& arr_0[i_0] = n", loopBodyFacts.get(0).getPathCond());
        assertContains("& !arr_0[i_0] = n", loopBodyFacts.get(1).getPathCond());
    }

    @Test
    public void testFindStrongerInv3() {
        final AnalyzerResult result = analyzeMethod(
            "findMethods/FindMethods.java",
            "FindMethods::find_stronger_inv_3([II)I");

        assertEquals(33.33d, result.coveredStrength(), .01d);
        assertEquals(50d, result.strength(), 0d);
        
        assertEquals(0, result.unclosedLoopInvPreservedGoals());
        assertEquals(0, result.problematicExceptions().size());

        final List<Fact> abstrLoopBodyFacts = result
                .getAbstractlyCoveredFactsOfType(LOOP_BODY_FACT);
        final List<Fact> abstrPostCondFacts = result
                .getAbstractlyCoveredFactsOfType(POST_COND_FACT);
        final List<Fact> uncPostCondFacts = result
                .getUncoveredFactsOfType(POST_COND_FACT);
        final List<Fact> uncLoopBodyFacts = result
                .getUncoveredFactsOfType(LOOP_BODY_FACT);

        assertEquals(0, abstrLoopBodyFacts.size());
        assertEquals(2, abstrPostCondFacts.size());

        assertEquals(0, uncPostCondFacts.size());
        assertEquals(2, uncLoopBodyFacts.size());

        assertEquals(2, result.numUncoveredFacts());
        assertEquals(2, result.numAbstractlyCoveredFacts());

        uncLoopBodyFacts.forEach(f -> {
            assertEquals("i = 1 + i_0", f.getDescr());
        });
    }

    @Test
    public void testFindStrongerInv2() {
        final AnalyzerResult result = analyzeMethod(
            "findMethods/FindMethods.java",
            "FindMethods::find_stronger_inv_2([II)I");

        assertEquals(0d, result.coveredStrength(), 0d);
        assertEquals(16.66d, result.strength(), .01d);
        
        assertEquals(0, result.unclosedLoopInvPreservedGoals());
        assertEquals(0, result.problematicExceptions().size());

        final List<Fact> abstrLoopBodyFacts = result
                .getAbstractlyCoveredFactsOfType(LOOP_BODY_FACT);
        final List<Fact> abstrPostCondFacts = result
                .getAbstractlyCoveredFactsOfType(POST_COND_FACT);
        final List<Fact> uncPostCondFacts = result
                .getUncoveredFactsOfType(POST_COND_FACT);
        final List<Fact> uncLoopBodyFacts = result
                .getUncoveredFactsOfType(LOOP_BODY_FACT);

        assertEquals(0, abstrLoopBodyFacts.size());
        assertEquals(2, abstrPostCondFacts.size());

        assertEquals(0, uncPostCondFacts.size());
        assertEquals(4, uncLoopBodyFacts.size());

        assertEquals(4, result.numUncoveredFacts());
        assertEquals(2, result.numAbstractlyCoveredFacts());
    }

    @Test
    public void testFindStrongerInv2a() {
        final AnalyzerResult result = analyzeMethod(
            "findMethods/FindMethods.java",
            "FindMethods::find_stronger_inv_2a([II)I");

        assertEquals(0d, result.coveredStrength(), 0d);
        assertEquals(33.33d, result.strength(), .01d);
        
        assertEquals(0, result.unclosedLoopInvPreservedGoals());

        assertEquals(1, result.problematicExceptions().size());
        assertContains("arr_0 != null, but i Out of Bounds",
            result.problematicExceptions().get(0).getExcLabel());
        assertContains("arr_0.length > i_0 & i_0 < 0",
            result.problematicExceptions().get(0).getPathCondition());

        final List<Fact> abstrLoopBodyFacts = result
                .getAbstractlyCoveredFactsOfType(LOOP_BODY_FACT);
        final List<Fact> abstrPostCondFacts = result
                .getAbstractlyCoveredFactsOfType(POST_COND_FACT);
        final List<Fact> uncPostCondFacts = result
                .getUncoveredFactsOfType(POST_COND_FACT);
        final List<Fact> uncLoopBodyFacts = result
                .getUncoveredFactsOfType(LOOP_BODY_FACT);

        assertEquals(2, abstrLoopBodyFacts.size());
        assertEquals(2, abstrPostCondFacts.size());

        assertEquals(0, uncPostCondFacts.size());
        assertEquals(2, uncLoopBodyFacts.size());

        assertEquals(2, result.numUncoveredFacts());
        assertEquals(4, result.numAbstractlyCoveredFacts());
    }

    @Test
    public void testFindStrongerInv() {
        final AnalyzerResult result = analyzeMethod(
            "findMethods/FindMethods.java",
            "FindMethods::find_stronger_inv([II)I");

        assertEquals(0d, result.coveredStrength(), 0d);
        assertEquals(33.33d, result.strength(), .01d);
        
        assertEquals(0, result.unclosedLoopInvPreservedGoals());

        assertEquals(1, result.problematicExceptions().size());
        assertContains("arr_0 != null, but i Out of Bounds",
            result.problematicExceptions().get(0).getExcLabel());
        assertContains("arr_0.length > i_0 & i_0 < 0",
            result.problematicExceptions().get(0).getPathCondition());

        final List<Fact> abstrLoopBodyFacts = result
                .getAbstractlyCoveredFactsOfType(LOOP_BODY_FACT);
        final List<Fact> uncLoopBodyFacts = result
                .getUncoveredFactsOfType(LOOP_BODY_FACT);
        final List<Fact> abstrPostCondFacts = result
                .getAbstractlyCoveredFactsOfType(POST_COND_FACT);
        final List<Fact> uncPostCondFacts = result
                .getUncoveredFactsOfType(POST_COND_FACT);

        assertEquals(2, abstrLoopBodyFacts.size());
        assertEquals(2, uncLoopBodyFacts.size());
        assertEquals(2, abstrPostCondFacts.size());

        assertEquals(0, uncPostCondFacts.size());

        assertEquals(2, result.numUncoveredFacts());
        assertEquals(4, result.numAbstractlyCoveredFacts());

        uncLoopBodyFacts.forEach(f -> {
            assertEquals("i = 1 + i_0", f.getDescr());
        });
    }

    @Test
    public void testFindSensiblePost() {
        final AnalyzerResult result = analyzeMethod(
            "findMethods/FindMethods.java",
            "FindMethods::find_sensible_post([II)I");

        assertEquals(0d, result.coveredStrength(), 0d);
        assertEquals(8.33d, result.strength(), .01d);
        
        assertEquals(0, result.unclosedLoopInvPreservedGoals());

        assertEquals(1, result.problematicExceptions().size());
        assertContains("arr_0 != null, but i Out of Bounds",
            result.problematicExceptions().get(0).getExcLabel());
        assertContains("arr_0.length > i_0 & i_0 < 0",
            result.problematicExceptions().get(0).getPathCondition());

        final List<Fact> abstrPostCondFacts = result
                .getAbstractlyCoveredFactsOfType(POST_COND_FACT);
        final List<Fact> uncLoopBodyFacts = result
                .getUncoveredFactsOfType(LOOP_BODY_FACT);
        final List<Fact> uncPostCondFacts = result
                .getUncoveredFactsOfType(POST_COND_FACT);

        assertEquals(1, abstrPostCondFacts.size());

        assertEquals(1, uncPostCondFacts.size());
        assertEquals(4, uncLoopBodyFacts.size());

        assertEquals(5, result.numUncoveredFacts());
        assertEquals(1, result.numAbstractlyCoveredFacts());

        assertEquals("result = result_1_0", uncPostCondFacts.get(0).getDescr());

        assertEquals("!result_1_0 = -1", uncPostCondFacts.get(0).getPathCond());

        assertEquals("result = -1", abstrPostCondFacts.get(0).getDescr());
        assertContains("result_1_0 = -1",
            abstrPostCondFacts.get(0).getPathCond());

        assertEquals("i = 1 + i_0", uncLoopBodyFacts.get(0).getDescr());
        assertEquals("result_1 = i_0", uncLoopBodyFacts.get(1).getDescr());
        assertEquals("i = 1 + i_0", uncLoopBodyFacts.get(2).getDescr());
        assertEquals("result_1 = -1", uncLoopBodyFacts.get(3).getDescr());

        assertContains("& arr_0[i_0] = n",
            uncLoopBodyFacts.get(0).getPathCond());
        assertContains("& arr_0[i_0] = n",
            uncLoopBodyFacts.get(1).getPathCond());
        assertContains("& !arr_0[i_0] = n",
            uncLoopBodyFacts.get(2).getPathCond());
        assertContains("& !arr_0[i_0] = n",
            uncLoopBodyFacts.get(3).getPathCond());
    }

    @Test
    public void testFindWeakest() {
        final AnalyzerResult result = analyzeMethod(
            "findMethods/FindMethods.java", "FindMethods::find_weakest([II)I");

        assertEquals(0d, result.coveredStrength(), 0d);
        assertEquals(0d, result.strength(), 0d);
        
        assertEquals(0, result.unclosedLoopInvPreservedGoals());

        assertEquals(1, result.problematicExceptions().size());
        assertContains("arr_0 != null, but i Out of Bounds",
            result.problematicExceptions().get(0).getExcLabel());
        assertContains("arr_0.length > i_0 & i_0 < 0",
            result.problematicExceptions().get(0).getPathCondition());

        final List<Fact> loopBodyFacts = result
                .getUncoveredFactsOfType(LOOP_BODY_FACT);
        final List<Fact> postCondFacts = result
                .getUncoveredFactsOfType(POST_COND_FACT);

        assertEquals(4, loopBodyFacts.size());
        assertEquals(2, postCondFacts.size());

        assertEquals(6, result.numUncoveredFacts());

        assertEquals("result = -1", postCondFacts.get(0).getDescr());
        assertEquals("result = result_1_0", postCondFacts.get(1).getDescr());
        assertContains("result_1_0 = -1", postCondFacts.get(0).getPathCond());
        assertContains("!result_1_0 = -1", postCondFacts.get(1).getPathCond());

        assertContains("& arr_0[i_0] = n",
                loopBodyFacts.get(0).getPathCond());
        assertContains("& arr_0[i_0] = n",
                loopBodyFacts.get(1).getPathCond());
        assertContains("& !arr_0[i_0] = n",
                loopBodyFacts.get(2).getPathCond());
        assertContains("& !arr_0[i_0] = n",
                loopBodyFacts.get(3).getPathCond());

        assertContains("& arr_0[i_0] = n", loopBodyFacts.get(0).getPathCond());
        assertContains("& arr_0[i_0] = n", loopBodyFacts.get(1).getPathCond());
        assertContains("& !arr_0[i_0] = n", loopBodyFacts.get(2).getPathCond());
        assertContains("& !arr_0[i_0] = n", loopBodyFacts.get(3).getPathCond());
    }

}