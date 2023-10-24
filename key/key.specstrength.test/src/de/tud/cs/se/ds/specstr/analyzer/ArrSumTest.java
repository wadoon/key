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

import org.junit.Test;

import de.tud.cs.se.ds.specstr.analyzer.Analyzer.AnalyzerResult;
import de.tud.cs.se.ds.specstr.analyzer.Analyzer.Fact;
import de.tud.cs.se.ds.specstr.analyzer.Analyzer.FactType;

/**
 * A method that returns, for a given array, an array where at each position
 * there is the sum up to that index in the input array.
 *
 * @author Dominic Steinhoefel
 */
public class ArrSumTest extends AbstractAnalyzerTest {

    @Test
    public void testArrSumStd() {
        final AnalyzerResult result = analyzeMethod( //
            "arrSum/ArrSum.java", //
            "ArrSum::arrSumStd([I)[I");

        assertEquals(0d, result.coveredStrength(), 0.0d);
        assertEquals(16.66, result.strength(), 0.01d);

        assertEquals(4, result.numFacts());
        assertEquals(2, result.numUncoveredFacts());
        assertEquals(1, result.numAbstractlyCoveredFacts());
        assertEquals(1, result.numCoveredFacts());

        assertEquals(2,
            result.getUncoveredFactsOfType(FactType.LOOP_BODY_FACT).size());
        assertEquals(1,
            result.getAbstractlyCoveredFactsOfType(FactType.POST_COND_FACT)
                    .size());

        final Fact absCoveredPostCondFact = result
                .getAbstractlyCoveredFactsOfType(FactType.POST_COND_FACT)
                .get(0);
        assertContains("result = x_arr_2", absCoveredPostCondFact.getDescr());
        assertEquals("arr_0.length <= i_0",
            absCoveredPostCondFact.getPathCond());
    }

}
