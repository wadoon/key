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

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tud.cs.se.ds.specstr.analyzer.Analyzer.AnalyzerResult;

/**
 * TODO
 *
 * @author Dominic Steinhöfel
 */
public class FindMethodsTest extends AbstractAnalyzerTest {

    @Test
    public void testWeakPostCondFind() {
        final AnalyzerResult result = analyzeMethod(
                "findMethods/FindMethods.java",
                "FindMethods::find_weak_postcond([II)I");

        assertEquals(1, result.numUncoveredFacts());
        assertEquals(Analyzer.FactType.LOOP_BODY_FACT,
                result.getUnCoveredFacts().get(0).getFactType());
    }

    @Test
    public void testSimpleFind() {
        final AnalyzerResult result = analyzeMethod(
                "findMethods/FindMethods.java", "FindMethods::find([II)I");

        assertEquals(1,
                result.getUnCoveredFacts()
                        .stream().filter(
                                f -> f.getFactType() == Analyzer.FactType.LOOP_BODY_FACT)
                        .count());
        assertEquals(1,
                result.getUnCoveredFacts()
                        .stream().filter(
                                f -> f.getFactType() == Analyzer.FactType.POST_COND_FACT)
                        .count());
        assertEquals(6,
                result.getUnCoveredFacts()
                        .stream().filter(
                                f -> f.getFactType() == Analyzer.FactType.POST_COND_INV_FACT)
                        .count());
        
        assertEquals(8, result.numUncoveredFacts());
    }

    @Test
    public void testStrongInvFind() {
        final AnalyzerResult result = analyzeMethod(
                "findMethods/FindMethods.java",
                "FindMethods::find_strong_inv([II)I");

        assertEquals(0,
                result.getUnCoveredFacts()
                        .stream().filter(
                                f -> f.getFactType() == Analyzer.FactType.LOOP_BODY_FACT)
                        .count());
        assertEquals(1,
                result.getUnCoveredFacts()
                        .stream().filter(
                                f -> f.getFactType() == Analyzer.FactType.POST_COND_FACT)
                        .count());
        assertEquals(9,
                result.getUnCoveredFacts()
                        .stream().filter(
                                f -> f.getFactType() == Analyzer.FactType.POST_COND_INV_FACT)
                        .count());
        
        assertEquals(10, result.numUncoveredFacts());
    }

    @Test
    public void testFindStronger() {
        final AnalyzerResult result = analyzeMethod(
                "findMethods/FindMethods.java",
                "FindMethods::find_stronger([II)I");

        assertEquals(1, result.numUncoveredFacts());
        
        assertEquals(1,
                result.getUnCoveredFacts()
                        .stream().filter(
                                f -> f.getFactType() == Analyzer.FactType.POST_COND_INV_FACT)
                        .count());
        
    }

    @Test
    public void testFindStrongest() {
        final AnalyzerResult result = analyzeMethod(
                "findMethods/FindMethods.java",
                "FindMethods::find_strongest([II)I");

        assertEquals(0, result.numUncoveredFacts());
    }

}
