// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.njml.JmlParsingFacade;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import org.junit.Test;
import org.key_project.util.collection.ImmutableList;

import static junit.framework.TestCase.assertEquals;
import static junit.framework.TestCase.assertSame;
import static org.junit.Assert.*;


public class TestJMLPreTranslator {
    private ImmutableList<TextualJMLConstruct> parseMethodSpec(String ms) throws SLTranslationException {
        return JmlParsingFacade.parseClasslevel(ms);
    }

    @Test
    public void testSimpleSpec() throws SLTranslationException {
        ImmutableList<TextualJMLConstruct> constructs
                = parseMethodSpec("/*@ normal_behavior\n"
                + "     requires true;\n"
                + "  */");

        assertNotNull(constructs);
        assertEquals(1, constructs.size());
        assertTrue(constructs.head() instanceof TextualJMLSpecCase);
        TextualJMLSpecCase specCase = (TextualJMLSpecCase) constructs.head();

        assertSame(specCase.getBehavior(), Behavior.NORMAL_BEHAVIOR);
        assertEquals(1, specCase.getRequires().size());
        assertEquals(0, specCase.getAssignable().size());
        assertEquals(0, specCase.getEnsures().size());
        assertEquals(0, specCase.getSignals().size());
        assertEquals(0, specCase.getSignalsOnly().size());

        assertEquals("requires true;", specCase.getRequires().head().text.trim());
    }


    @Test
    public void testComplexSpec() throws SLTranslationException {
        ImmutableList<TextualJMLConstruct> constructs
                = parseMethodSpec("/*@ behaviour\n"
                + "  @  requires true;\n"
                + "  @  requires ((;;(;););(););\n"
                + "  @  ensures false;\n"
                + "  @  signals exception;\n"
                + "  @  signals_only onlythis;\n"
                + "  @  assignable \\nothing;\n"
                + "  @*/");

        assertNotNull(constructs);
        assertEquals(1, constructs.size());
        assertTrue(constructs.head() instanceof TextualJMLSpecCase);
        TextualJMLSpecCase specCase = (TextualJMLSpecCase) constructs.head();

        assertSame(specCase.getBehavior(), Behavior.BEHAVIOR);
        assertEquals(2, specCase.getRequires().size());
        assertEquals(1, specCase.getAssignable().size());
        assertEquals(1, specCase.getEnsures().size());
        assertEquals(1, specCase.getSignals().size());
        assertEquals(1, specCase.getSignalsOnly().size());

        assertEquals("ensures false;", specCase.getEnsures().head().text.trim());
        assertEquals("assignable \\nothing;", specCase.getAssignable().head().text.trim());
    }


    @Test public void testMultipleSpecs() throws SLTranslationException {
        ImmutableList<TextualJMLConstruct> constructs
                = parseMethodSpec("//@ normal_behaviour\n"
                + "//@  ensures false\n"
                + "//@          || true;\n"
                + "//@  assignable \\nothing;\n"
                + "//@ also exceptional_behaviour\n"
                + "//@  requires o == null;\n"
                + "//@  signals Exception;\n");

        assertNotNull(constructs);
        assertEquals(2, constructs.size());
        assertTrue(constructs.head() instanceof TextualJMLSpecCase);
        assertTrue(constructs.tail().head() instanceof TextualJMLSpecCase);
        TextualJMLSpecCase specCase1 = (TextualJMLSpecCase) constructs.head();
        TextualJMLSpecCase specCase2 = (TextualJMLSpecCase) constructs.tail().head();

        assertSame(specCase1.getBehavior(), Behavior.NORMAL_BEHAVIOR);
        assertEquals(0, specCase1.getRequires().size());
        assertEquals(1, specCase1.getAssignable().size());
        assertEquals(1, specCase1.getEnsures().size());
        assertEquals(0, specCase1.getSignals().size());
        assertEquals(0, specCase1.getSignalsOnly().size());

        assertSame(specCase2.getBehavior(), Behavior.EXCEPTIONAL_BEHAVIOR);
        assertEquals(1, specCase2.getRequires().size());
        assertEquals(0, specCase2.getAssignable().size());
        assertEquals(0, specCase2.getEnsures().size());
        assertEquals(1, specCase2.getSignals().size());
        assertEquals(0, specCase2.getSignalsOnly().size());
    }

    @Test public void testAtInModelmethod() throws SLTranslationException {
        parseMethodSpec(
                "/*@ model_behaviour\n" +
                        "  @   requires true;\n" +
                        "  @ model int f(int x) {\n" +
                        "  @   return x+1;\n" +
                        "  @ }\n" +
                        "  @*/");
    }

    // used to be accepted
    @Test public void disabled_testMLCommentEndInSLComment() throws Exception {
        try {
            parseMethodSpec(
                    "//@ requires @*/ true;");
            fail("Characters '@*/' should not be parsed");
        } catch (SLTranslationException ex) {
            // anticipated
        }

        try {
            parseMethodSpec(
                    "//@ requires */ true;");
            fail("Characters '*/' should not be parsed");
        } catch (SLTranslationException ex) {
            // anticipated
        }

    }

    @Test
    public void testFailure() {
        try {
            parseMethodSpec("/*@ normal_behaviour \n @ signals ohoh;" + "  @*/");
            fail();
        } catch (SLTranslationException e) {
            //fine
        }
    }

    @Test
    public void testFailure2() {
        try {
            parseMethodSpec("/*@ behaviour\n"
                    + "  @  requires (;((;;);();();(();;;(;)));\n"
                    + "  @*/");
            fail();
        } catch (SLTranslationException e) {
            //fine
        }
    }
}