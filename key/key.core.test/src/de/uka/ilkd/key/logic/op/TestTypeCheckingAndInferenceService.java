// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.op;

import java.io.File;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.logic.op.LogicVariable;
import org.key_project.common.core.logic.sort.SortImpl;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TestJavaInfo;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.util.HelperClassForTests;
import junit.framework.TestCase;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public class TestTypeCheckingAndInferenceService extends TestCase {
    private Services services;
    private TermBuilder tb;

    public void setUp() {
        HelperClassForTests helper = new HelperClassForTests();
        final ProofAggregate agg =
                helper.parse(new File(TestJavaInfo.testfile));
        services = agg.getFirstProof().getServices();
        tb = services.getTermBuilder();
    }

    public void testFunction() {
        final Function op = new Function(new Name("f"), SortImpl.ANY);

        final TypeCheckingAndInferenceService<Function> service =
                TypeCheckingAndInferenceService.getTypeCheckerFor(op);

        assertNotNull(service);

        assertSame(
                TypeCheckingAndInferenceService.AbstractSortedOperatorTypeCheckingAndInferenceService.class,
                service.getClass());

        assertTrue(service.validTopLevel(
                tb.var(new LogicVariable(new Name("v"), SortImpl.ANY)), op));

        assertSame(service.getClass(),
                TypeCheckingAndInferenceService
                        .getTypeCheckerFor(new LogicVariable(new Name("v1"),
                                SortImpl.ANY)).getClass());
    }
}
