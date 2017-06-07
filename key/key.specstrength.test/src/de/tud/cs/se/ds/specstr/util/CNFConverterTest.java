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

package de.tud.cs.se.ds.specstr.util;

import static org.junit.Assert.assertEquals;

import org.junit.Before;
import org.junit.Test;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.AbstractProfile;

/**
 * TODO
 *
 * @author Dominic Steinhöfel
 */
public class CNFConverterTest {
    private CNFConverter conv;
    private TermBuilder tb;
    private Services services;

    @Before
    public void setUp() throws Exception {
        services = new Services(AbstractProfile.getDefaultProfile());
        tb = services.getTermBuilder();
        conv = new CNFConverter(tb);
    }

    @Test
    public void testBiimplicationElimination() {
        final Term p = predicate("p");
        final Term q = predicate("q");

        // (p ==> q) && ((p <==> q) || p)
        final Term input = tb.and(tb.imp(p, q), tb.or(tb.equals(p, q), p));

        // (!p || q) && (((!p || q) && (!q || p)) || p)
        final Term output = tb.and( //
                tb.or(tb.not(p), q), //
                tb.or( //
                        tb.and( //
                                tb.or(tb.not(p), q), //
                                tb.or(tb.not(q), p)), //
                        p));

        final Term result = conv.eliminateBiImplications(input);

        assertEquals(output, result);
    }

    private Term predicate(String name) {
        return tb.func(new Function(new Name("p"), Sort.FORMULA));
    }
}
