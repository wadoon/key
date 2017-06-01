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
    public void testSimpleFind() {
        final AnalyzerResult result = analyzeMethod(
                "findMethods/FindMethods.java", "FindMethods::find([II)I");

        assertEquals(1, result.numUncoveredFacts());
        assertEquals(Analyzer.FactType.LOOP_BODY_FACT,
                result.getUnCoveredFacts().get(0).getFactType());
    }
    
    @Test
    public void testStrongFind() {
        final AnalyzerResult result = analyzeMethod(
                "findMethods/FindMethods.java", "FindMethods::find_strong([II)I");

        assertEquals(0, result.numUncoveredFacts());
    }
    
    @Test
    public void testFindInstanceWeak() {
        final AnalyzerResult result = analyzeMethod(
                "findMethods/FindMethods.java", "FindMethods::find_instance_weak([II)V");

        assertEquals(2, result.numUncoveredFacts());
        assertEquals(Analyzer.FactType.POST_COND_FACT,
                result.getUnCoveredFacts().get(0).getFactType());
        assertEquals(Analyzer.FactType.LOOP_BODY_FACT,
                result.getUnCoveredFacts().get(1).getFactType());
    }
    
    @Test
    public void testFindInstance() {
        final AnalyzerResult result = analyzeMethod(
                "findMethods/FindMethods.java", "FindMethods::find_instance([II)V");

        assertEquals(1, result.numUncoveredFacts());
        assertEquals(Analyzer.FactType.POST_COND_FACT,
                result.getUnCoveredFacts().get(0).getFactType());
    }
    
    @Test
    public void testFindInstanceStrong() {
        final AnalyzerResult result = analyzeMethod(
                "findMethods/FindMethods.java", "FindMethods::find_instance_strong([II)V");

        assertEquals(0, result.numUncoveredFacts());
    }
    
}
