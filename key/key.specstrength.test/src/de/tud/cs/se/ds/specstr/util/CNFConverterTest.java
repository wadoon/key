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
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
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

    private final Sort s = new SortImpl(new Name("S"));

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
        final Term expected = tb.and( //
                tb.or(tb.not(p), q), //
                tb.or( //
                        tb.and( //
                                tb.or(tb.not(p), q), //
                                tb.or(tb.not(q), p)), //
                        p));

        final Term result = conv.eliminateBiImplications(input);

        assertEquals(expected, result);
    }

    @Test
    public void testPushNegationInvards() {
        final Term p = predicate("p");
        final LogicVariable x = qv("x");
        final LogicVariable y = qv("y");
        final Term xT = tb.var(x);
        final Term yT = tb.var(y);

        // !(\forall x; (x != y && (!!p || (\exists y; x == y))))
        final Term input = //
                tb.not( //
                        tb.all(x,
                                tb.and( //
                                        tb.not(tb.equals(xT, yT)), //
                                        tb.or( //
                                                tb.not(tb.not(p)),
                                                tb.ex(y, tb.equals(xT, yT))))));

        // (\exists x; (x == y || (p && (\forall y; x != y))))
        final Term expected = //
                tb.ex(x, tb.or( //
                        tb.equals(xT, yT), //
                        tb.and( //
                                tb.not(p), //
                                tb.all(y, tb.not( //
                                        tb.equals(xT, yT))))));

        final Term result = conv.pushNegationsInvards(input);

        assertEquals(expected, result);
    }

    private LogicVariable qv(String name) {
        return new LogicVariable(new Name(name), s);
    }

    private Term predicate(String name) {
        return tb.func(new Function(new Name("p"), Sort.FORMULA));
    }
}
