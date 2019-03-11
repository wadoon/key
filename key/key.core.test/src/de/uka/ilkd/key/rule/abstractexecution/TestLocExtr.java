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

package de.uka.ilkd.key.rule.abstractexecution;

import org.antlr.runtime.RecognitionException;
import org.junit.Test;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.FieldLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.parser.AbstractTestTermParser;

/**
 * Test suite for the abstract execution taclets.
 *
 * @author Dominic Steinhoefel
 */
public class TestLocExtr extends AbstractTestTermParser {
    public TestLocExtr() {
        super(TestLocExtr.class.getName());
    }

    @Override
    public void setUp() throws RecognitionException {
        parseDecls(
                "\\programVariables {Heap heap; testTermParserHeap.A self;}");
    }

    @Test
    public void testFieldExtraction() throws Exception {
        final Services services = getServices();

        final String storeHeapExpr = "store(" + //
                "store(heap, self, testTermParserHeap.A::$f, Z(7(1(#))))," + //
                "self," + //
                "testTermParserHeap.A::$f1, Z(2(4(#))))";
        final Term parsedStoreHeapExpr = parseTerm(storeHeapExpr);

        final String selectHeapExpr = "java.lang.Object::select(" + //
                "store(heap, self, testTermParserHeap.A::$f, Z(7(1(#))))," + //
                "self," + //
                "testTermParserHeap.A::$f)";
        final Term parsedSelectHeapExpr = parseTerm(selectHeapExpr);

        final String locSetHeapExpr = "singleton(self,testTermParserHeap.A::$f)";
        final Term parsedLocSetExpr = parseTerm(locSetHeapExpr);

        final AbstractUpdateLoc[] storeTermLocs = AbstractUpdateFactory
                .abstractUpdateLocsFromUnionTerm(parsedStoreHeapExpr, services)
                .toArray(new AbstractUpdateLoc[0]);
        final AbstractUpdateLoc[] selectTermLocs = AbstractUpdateFactory
                .abstractUpdateLocsFromUnionTerm(parsedSelectHeapExpr, services)
                .toArray(new AbstractUpdateLoc[0]);
        final AbstractUpdateLoc[] locSetTermLocs = AbstractUpdateFactory
                .abstractUpdateLocsFromUnionTerm(parsedLocSetExpr, services)
                .toArray(new AbstractUpdateLoc[0]);

        assertEquals(3, storeTermLocs.length);
        assertEquals(FieldLoc.class, storeTermLocs[0].getClass());
        assertEquals("(self, f1)", storeTermLocs[0].toString());
        assertEquals(FieldLoc.class, storeTermLocs[1].getClass());
        assertEquals("(self, f)", storeTermLocs[1].toString());
        assertEquals(PVLoc.class, storeTermLocs[2].getClass());
        assertEquals("heap", storeTermLocs[2].toString());

        assertEquals(2, selectTermLocs.length);
        assertEquals(FieldLoc.class, selectTermLocs[0].getClass());
        assertEquals("(self, f)", selectTermLocs[0].toString());
        assertEquals(PVLoc.class, selectTermLocs[1].getClass());
        assertEquals("heap", selectTermLocs[1].toString());

        assertEquals(1, locSetTermLocs.length);
        assertEquals(FieldLoc.class, locSetTermLocs[0].getClass());
        assertEquals("(self, f)", locSetTermLocs[0].toString());
    }
}