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

        assertEquals(1, result.getUncoveredFactsOfType(LOOP_BODY_FACT).size());
        assertEquals(2, result.getUncoveredFactsOfType(POST_COND_FACT).size());
        assertEquals(7,
                result.getUncoveredFactsOfType(POST_COND_INV_FACT).size());

        assertEquals(9, result.numUncoveredFacts());
    }

    @Test
    public void testSimpleFind() {
        final AnalyzerResult result = analyzeMethod(
                "findMethods/FindMethods.java", "FindMethods::find([II)I");

        assertEquals(1, result.getUncoveredFactsOfType(LOOP_BODY_FACT).size());
        assertEquals(1, result.getUncoveredFactsOfType(POST_COND_FACT).size());
        assertEquals(7,
                result.getUncoveredFactsOfType(POST_COND_INV_FACT).size());

        assertEquals(8, result.numUncoveredFacts());
    }

    @Test
    public void testStrongInvFind() {
        final AnalyzerResult result = analyzeMethod(
                "findMethods/FindMethods.java",
                "FindMethods::find_strong_inv([II)I");

        assertEquals(0, result.getUncoveredFactsOfType(LOOP_BODY_FACT).size());
        assertEquals(1, result.getUncoveredFactsOfType(POST_COND_FACT).size());
        assertEquals(10,
                result.getUncoveredFactsOfType(POST_COND_INV_FACT).size());

        assertEquals(10, result.numUncoveredFacts());
    }

    @Test
    public void testFindStronger() {
        final AnalyzerResult result = analyzeMethod(
                "findMethods/FindMethods.java",
                "FindMethods::find_stronger([II)I");

        assertEquals(1,
                result.getUncoveredFactsOfType(POST_COND_INV_FACT).size());
        
        assertEquals(1, result.numUncoveredFacts());

    }

    @Test
    public void testFindStrongest() {
        final AnalyzerResult result = analyzeMethod(
                "findMethods/FindMethods.java",
                "FindMethods::find_strongest([II)I");

        assertEquals(0, result.numUncoveredFacts());
    }

}
