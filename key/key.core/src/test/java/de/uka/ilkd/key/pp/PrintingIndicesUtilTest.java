package de.uka.ilkd.key.pp;

import junitparams.JUnitParamsRunner;
import junitparams.Parameters;
import org.junit.Test;
import org.junit.runner.RunWith;

import static de.uka.ilkd.key.pp.PrintingIndicesUtil.rewriteIndices;
import static org.junit.Assert.assertEquals;


/**
 * @author Alexander Weigl
 * @version 1 (03.07.19)
 */
@RunWith(JUnitParamsRunner.class)
public class PrintingIndicesUtilTest {


    @Test
    @Parameters({"abc, abc",
            ",",
            "₁,_1",
            "₂,_2",
            "abc₉₉, abc_99",
            "abc₉₉₆, abc_996",
            "abc₁₂₃₄₅₆₇₈₉₀, abc_1234567890",
            "abc_def₁₁,abc_def_11",
            "abc_def_₁₁,abc_def__11",
            "abc_def__11g,abc_def__11g"
    })
    public void testRewriteIndices(String exp, String variable) {
        assertEquals(exp, rewriteIndices(variable));
        /*assertEquals("", rewriteIndices(""));
        assertEquals("₁", rewriteIndices("_1"));
        assertEquals("₂", rewriteIndices("_2"));
        assertEquals("abc₉₉", rewriteIndices("abc_99"));
        assertEquals("abc₆₉₉", rewriteIndices("abc_996"));
        assertEquals("abc", rewriteIndices("abc_1234567890"));
        assertEquals("abc_def₁₁", rewriteIndices("abc_def_11"));
        assertEquals("abc", rewriteIndices("abc_def__11"));
        assertEquals("abc_def__11g", rewriteIndices("abc_def__11g"));*/
    }
}