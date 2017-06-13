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

import static de.tud.cs.se.ds.specstr.analyzer.Analyzer.FactType.LOOP_BODY_FACT;
import static de.tud.cs.se.ds.specstr.analyzer.Analyzer.FactType.POST_COND_FACT;
import static org.hamcrest.Matchers.containsString;
import static org.hamcrest.Matchers.equalTo;

import java.util.List;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ErrorCollector;

import de.tud.cs.se.ds.specstr.analyzer.Analyzer.AnalyzerResult;
import de.tud.cs.se.ds.specstr.analyzer.Analyzer.Fact;

/**
 * TODO
 *
 * @author Dominic Steinhöfel
 */
public class FindMethodsTest2 extends AbstractAnalyzerTest {
    @Rule
    public final ErrorCollector collector = new ErrorCollector();

    private void assertEquals(int expected, int actual) {
        collector.checkThat(actual, equalTo(expected));
    }

    private void assertEquals(String expected, String actual) {
        collector.checkThat(actual, equalTo(expected));
    }

    @Test
    public void testFind() {
        final AnalyzerResult result = analyzeMethod(
                "findMethods/FindMethods2.java", "FindMethods2::find([II)I");

        final List<Fact> loopBodyFacts = result
                .getUncoveredFactsOfType(LOOP_BODY_FACT);

        assertEquals(2, loopBodyFacts.size());
        assertEquals(0, result.getUncoveredFactsOfType(POST_COND_FACT).size());

        assertEquals(2, result.numUncoveredFacts());

        loopBodyFacts.forEach(f -> {
            assertEquals("i = 1 + i_0", f.getDescr());
        });

        collector.checkThat(loopBodyFacts.get(0).getPathCond(),
                containsString("& !arr_0[i_0] = n"));

        collector.checkThat(loopBodyFacts.get(1).getPathCond(),
                containsString("& arr_0[i_0] = n"));
    }

}
