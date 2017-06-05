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
public class LoopFreeTest extends AbstractAnalyzerTest {

    @Test
    public void testAbsWeakPost() {
        final AnalyzerResult result = analyzeMethod( //
                "loopFree/SimpleMath.java", //
                "SimpleMath::abs(I)I");

        assertEquals(2, result.getUncoveredFactsOfType(POST_COND_FACT).size());
        assertEquals(2, result.numUncoveredFacts());
    }

}
