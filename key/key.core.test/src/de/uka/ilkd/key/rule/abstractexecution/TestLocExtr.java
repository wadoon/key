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

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
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
        final String storeHeapExpr = "store(" + //
                "store(heap, self, testTermParserHeap.A::$f, Z(7(1(#))))," + //
                "self," + //
                "testTermParserHeap.A::$f1, Z(2(4(#))))";
        final Term parsedStoreHeapExpr = parseTerm(storeHeapExpr);

        final String locSetHeapExpr = "singleton(self,testTermParserHeap.A::$f)";
        final Term parsedLocSetExpr = parseTerm(locSetHeapExpr);

        final JavaInfo javaInfo = getServices().getJavaInfo();
        final KeYJavaType kjt = javaInfo
                .getKeYJavaType("testTermParserHeap.A");
        javaInfo.getCanonicalFieldProgramVariable("f", kjt);

        System.out.println();
    }
}