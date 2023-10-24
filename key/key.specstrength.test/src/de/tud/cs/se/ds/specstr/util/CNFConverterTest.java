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
 * @author Dominic Steinhoefel
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
    public void testCNFConversion() {
        final Term p = predicate("p");
        final Term q = predicate("q");
        final LogicVariable x = qv("x");

        // !(p ==> !q) || !(\forall x; p && !q)
        final Term input = tb.or(tb.not(tb.imp(p, tb.not(q))),
                tb.not(tb.all(x, tb.and(p, tb.not(q)))));

        // (p || ((\exists x; !p) || (\exists x; q))) &&
        // (q || ((\exists x; !p) || (\exists x; q)))
        final Term expected = tb.and(
                tb.or(p, tb.or(tb.ex(x, tb.not(p)), tb.ex(x, q))),
                tb.or(q, tb.or(tb.ex(x, tb.not(p)), tb.ex(x, q))));

        final Term result = conv.convertToCNF(input);

        assertEquals(expected, result);
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

    @Test
    public void testSplitQuantifiers() {
        final Term p = predicate("p");
        final Term q = predicate("q");
        final LogicVariable x = qv("x");

        // (\forall x; (p && (\exists x; q || p)))
        final Term input = //
                tb.all(x, tb.and(p, tb.ex(x, tb.or(q, p))));

        // (\forall x; p) && (\forall x; ((\exists x; q) || (\exists x; p)))
        final Term expected = //
                tb.and(tb.all(x, p),
                        tb.all(x, tb.or(tb.ex(x, q), tb.ex(x, p))));

        final Term result = conv.splitQuantifiers(input);

        assertEquals(expected, result);
    }

    @Test
    public void testApplyDistributivity() {
        final Term a = predicate("a");
        final Term b = predicate("b");
        final Term c = predicate("c");
        final Term d = predicate("d");

        // (a && b) || (c && d)
        final Term input = //
                tb.or(tb.and(a, b), tb.and(c, d));

        // (a || c) && (a || d) && (b || c) && (b || d)
        final Term expected = //
                tb.and( //
                        tb.and(tb.or(a, c), tb.or(a, d)),
                        tb.and(tb.or(b, c), tb.or(b, d)));

        final Term result = conv.applyDistributivityLaws(input);

        assertEquals(expected, result);
    }

    private LogicVariable qv(String name) {
        return new LogicVariable(new Name(name), s);
    }

    private Term predicate(String name) {
        return tb.func(new Function(new Name(name), Sort.FORMULA));
    }
}
