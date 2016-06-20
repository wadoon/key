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

package de.uka.ilkd.key.logic;

import java.util.ArrayList;

import junit.framework.TestCase;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.calculus.CCSemisequentChangeInfo;
import org.key_project.common.core.logic.calculus.SequentFormula;
import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.rule.TacletForTests;

public class TestSemisequent extends TestCase {

    private TermBuilder TB;

    private ArrayList<SequentFormula<Term>> con;

    public TestSemisequent(String name) {
        super(name);
    }

    public void setUp() {
        TB = TacletForTests.services().getTermBuilder();
        Function p = new Function(new Name("p"), Sort.FORMULA, new Sort[] {});
        Function q = new Function(new Name("q"), Sort.FORMULA, new Sort[] {});
        Function r = new Function(new Name("r"), Sort.FORMULA, new Sort[] {});

        Function a = new Function(new Name("a"), Sort.FORMULA, new Sort[] {});
        Function b = new Function(new Name("b"), Sort.FORMULA, new Sort[] {});
        Function c = new Function(new Name("c"), Sort.FORMULA, new Sort[] {});

        Term t_p = TB.func(p, new Term[] {});
        Term t_q = TB.func(q, new Term[] {});
        Term t_r = TB.func(r, new Term[] {});

        Term t_a = TB.func(a, new Term[] {});
        Term t_b = TB.func(b, new Term[] {});
        Term t_c = TB.func(c, new Term[] {});

        con = new ArrayList<SequentFormula<Term>>();
        con.add(new SequentFormula<>(t_p));
        con.add(new SequentFormula<>(t_q));
        con.add(new SequentFormula<>(t_r));
        con.add(new SequentFormula<>(t_r));
        con.add(new SequentFormula<>(t_a));
        con.add(new SequentFormula<>(t_b));
        con.add(new SequentFormula<>(t_c));

        Sort s = new SortImpl(new Name("test"));
        Function f = new Function(new Name("f"), s, new Sort[] {});
        Term t_f = TB.func(f, new Term[] {});
    }

    public void tearDown() {
        con = null;
    }

    private Semisequent extract(CCSemisequentChangeInfo<SequentFormula<Term>, Semisequent> semiCI) {
        return semiCI.semisequent();
    }

    public void testContains() {
        Semisequent seq = Semisequent.nil();
        seq = extract(seq.insert(0, con.get(0)));
        seq = extract(seq.insert(1, con.get(1)));
        SequentFormula<Term> eq2con0 =
                new SequentFormula<Term>(con.get(0).formula());
        assertTrue("Contains should test of identity and not equality.",
                !seq.contains(eq2con0));
    }

    public void testContainsEquals() {
        Semisequent seq = Semisequent.nil();
        seq = extract(seq.insert(0, con.get(0)));
        seq = extract(seq.insert(1, con.get(1)));
        SequentFormula<Term> eq2con0 =
                new SequentFormula<>(con.get(0).formula());
        assertTrue("Contains tests of equality and should find the formula.",
                seq.containsEqual(eq2con0));
    }

    public void testGet() {
        Semisequent seq = Semisequent.nil();
        seq = extract(seq.insert(0, con.get(0)));
        seq = extract(seq.insert(1, con.get(1)));
        assertSame(seq.get(0), con.get(0));
        assertSame(seq.get(1), con.get(1));

        try {
            seq.get(2);
        }
        catch (IndexOutOfBoundsException iob) {
            return;
        }
        fail();
    }

    public void testindexOf() {
        Semisequent seq = Semisequent.nil();
        seq = extract(seq.insert(0, con.get(0)));
        seq = extract(seq.insert(1, con.get(1)));
        seq = extract(seq.insert(2, con.get(2)));
        assertTrue("Semisequent has wrong size.", seq.size() == 3);
        assertTrue("con.get(0) has wrong index in semisequent. Expected 0" +
                " has " + seq.indexOf(con.get(0)), seq.indexOf(con.get(0)) == 0);
        assertTrue("con.get(1) has wrong index in semisequent. Expected 1" +
                " has " + seq.indexOf(con.get(1)), seq.indexOf(con.get(1)) == 1);
        assertTrue("con.get(2) has wrong index in semisequent. Expected 2" +
                " has " + seq.indexOf(con.get(2)), seq.indexOf(con.get(2)) == 2);
    }

    public void testRemove() {

        Semisequent seq = Semisequent.nil();
        seq = extract(seq.insert(0, con.get(0)));
        seq = extract(seq.insert(1, con.get(1)));
        seq = extract(seq.insert(2, con.get(2)));
        seq = extract(seq.remove(1));

        assertTrue("Semisequent has wrong size.", seq.size() == 2);
        assertTrue("Semisequent contains deleted element.",
                !seq.contains(con.get(1)));
        assertTrue("con.get(1) has wrong index in semisequent",
                seq.indexOf(con.get(1)) == -1);
        assertTrue("con.get(0) has wrong index in semisequent",
                seq.indexOf(con.get(0)) == 0);
        assertTrue("con.get(2) has wrong index in semisequent",
                seq.indexOf(con.get(2)) == 1);
    }

    public void testReplace() {
        Semisequent seq = Semisequent.nil();
        seq = extract(seq.insert(0, con.get(0)));
        seq = extract(seq.insert(1, con.get(1)));
        seq = extract(seq.replace(1, con.get(2)));

        assertTrue("Semisequent has wrong size.", seq.size() == 2);
        assertTrue("Semisequent contains deleted element.",
                !seq.contains(con.get(1)));
        assertTrue("con.get(1) has wrong index in semisequent",
                seq.indexOf(con.get(1)) == -1);
        assertTrue("con.get(0) has wrong index in semisequent",
                seq.indexOf(con.get(0)) == 0);
        assertTrue("con.get(2) has wrong index in semisequent",
                seq.indexOf(con.get(2)) == 1);
    }

    public void testNoDuplicates() {
        Semisequent seq = Semisequent.nil();
        seq = extract(seq.insert(0, con.get(0)));
        seq = extract(seq.insert(1, con.get(1)));
        seq = extract(seq.insert(2, con.get(1)));

        assertTrue("Semisequent has duplicate", seq.size() == 2);
    }

    public void testImmutable() {
        Semisequent seq = Semisequent.nil();
        Semisequent old = Semisequent.nil();
        seq = extract(seq.insert(0, con.get(0)));
        seq = extract(seq.insert(1, con.get(1)));
        old = seq;
        seq = extract(seq.insert(2, con.get(2)));

        assertTrue("Semisequent seems not to be immutable.", old.size() == 2);
    }

    public void testUniqueEmpty() {
        Semisequent seq = Semisequent.nil();
        seq = extract(seq.insert(0, con.get(0)));
        seq = extract(seq.remove(0));
        assertSame("Semisequent is empty but not the EMPTY_SEMISEQUENT.", seq,
                Semisequent.nil());

    }

    public void testEquals() {
        Semisequent seq1 = Semisequent.nil();
        seq1 = extract(seq1.insert(0, con.get(0)));
        seq1 = extract(seq1.insert(0, con.get(1)));
        seq1 = extract(seq1.insert(0, con.get(2)));
        Semisequent seq2 = Semisequent.nil();
        seq2 = extract(seq2.insert(0, con.get(0)));
        seq2 = extract(seq2.insert(0, con.get(1)));
        seq2 = extract(seq2.insert(0, con.get(2)));
        Semisequent seq3 = Semisequent.nil();
        seq3 = extract(seq3.insert(0, con.get(0)));
        seq3 = extract(seq3.insert(0, con.get(1)));
        seq3 = extract(seq3.insert(0, con.get(3)));
        Semisequent seq4 = Semisequent.nil();
        seq4 = extract(seq4.insert(0, con.get(0)));
        seq4 = extract(seq4.insert(0, con.get(2)));
        seq4 = extract(seq4.insert(0, con.get(1)));

        assertEquals("seq1=seq1", seq1, seq1);
        assertEquals("seq1=seq2", seq1, seq2);
        assertEquals("seq1=seq3", seq1, seq3);
        assertTrue("seq1!=seq4", !seq1.equals(seq4));
    }

    public void testListInsert() {
        Semisequent origin =
                extract(extract(
                        extract(Semisequent.nil().insertLast(con.get(0))).
                                insertLast(con.get(1))).insertLast(con.get(2)));

        Semisequent expected =
                extract(extract(
                        extract(origin.insertLast(con.get(4))).insertLast(
                                con.get(5))).
                        insertLast(con.get(6)));
        ImmutableList<SequentFormula<Term>> insertionList =
                ImmutableSLList.<SequentFormula<Term>> nil().
                        prepend(con.get(0)).prepend(con.get(1))
                        .prepend(con.get(6)).prepend(con.get(5))
                        .prepend(con.get(4));
        Semisequent result =
                extract(origin.insert(origin.size(), insertionList));
        assertEquals("Both semisequents should be equal.", expected, result);

    }

    public void testListInsertInMid() {
        Semisequent origin =
                extract(extract(
                        extract(Semisequent.nil().insertLast(con.get(0))).
                                insertLast(con.get(1))).insertLast(con.get(2)));
        Semisequent expected =
                extract(extract(
                        extract(origin.insert(2, con.get(4))).insert(3,
                                con.get(5))).insert(4, con.get(6)));
        ImmutableList<SequentFormula<Term>> insertionList =
                ImmutableSLList.<SequentFormula<Term>> nil()
                        .prepend(con.get(0)).prepend(con.get(1))
                        .prepend(con.get(6)).prepend(con.get(5))
                        .prepend(con.get(4));
        Semisequent result =
                extract(origin.insert(origin.size() - 1, insertionList));
        assertEquals("Both semisequents should be equal.", expected, result);

    }

    public void testListReplace() {
        // [p,q,r]
        Semisequent origin =
                extract(extract(
                        extract(Semisequent.nil().insertLast(con.get(0))).
                                insertLast(con.get(1))).insertLast(con.get(2)));
        // [p,q,a,b,c]
        Semisequent expected =
                extract(extract(
                        extract(
                                extract(origin.remove(2))
                                        .insertLast(con.get(4))).
                                insertLast(con.get(5))).insertLast(con.get(6)));
        // insert: [a,b,c,q,p]
        ImmutableList<SequentFormula<Term>> insertionList =
                ImmutableSLList.<SequentFormula<Term>> nil().
                        prepend(con.get(0)).prepend(con.get(1))
                        .prepend(con.get(6)).prepend(con.get(5))
                        .prepend(con.get(4));

        CCSemisequentChangeInfo<SequentFormula<Term>, Semisequent> result =
                origin.replace(origin.size() - 1, insertionList);

        assertEquals(
                "SemisequentChangeInfo is corrupt due to wrong added formula list:",
                ImmutableSLList.<SequentFormula<Term>> nil()
                        .prepend(con.get(4)).
                        prepend(con.get(5)).prepend(con.get(6)),
                result.addedFormulas());
        assertEquals(
                "SemisequentChangeInfo is corrupt due to wrong removed formula list:",
                ImmutableSLList.<SequentFormula<Term>> nil().prepend(
                        con.get(2)),
                result.removedFormulas());
        assertEquals("Both semisequents should be equal.", expected,
                extract(result));

    }

    public void testListReplaceAddRedundantList() {
        // [p,q]
        Semisequent origin =
                extract(extract(Semisequent.nil().insertLast(con.get(0))).
                        insertLast(con.get(1)));
        // [exp.: p,q,a,b,c,r]
        Semisequent expected =
                extract(extract
                (extract(extract(origin.insertLast(con.get(4))).
                        insertLast(con.get(5))).insertLast(con.get(6)))
                        .insertLast(con.get(2)));
        // insert:[a,b,c,r,r,q,p]
        ImmutableList<SequentFormula<Term>> insertionList =
                ImmutableSLList.<SequentFormula<Term>> nil().
                        prepend(con.get(0)).prepend(con.get(1))
                        .prepend(con.get(2)).prepend(con.get(3))
                        .prepend(con.get(6)).prepend(con.get(5))
                        .prepend(con.get(4));

        CCSemisequentChangeInfo<SequentFormula<Term>, Semisequent> sci =
                origin.replace(origin.size(), insertionList);
        assertEquals(
                "SemisequentChangeInfo is corrupt due to wrong added formula list:",
                ImmutableSLList.<SequentFormula<Term>> nil()
                        .prepend(con.get(4)).prepend(con.get(5)).
                        prepend(con.get(6)).prepend(con.get(3)),
                sci.addedFormulas());
        assertEquals(
                "SemisequentChangeInfo is corrupt due to wrong removed formula list:",
                ImmutableSLList.<SequentFormula<Term>> nil(),
                sci.removedFormulas());
        assertEquals("Both semisequents should be equal.", expected,
                extract(sci));
    }

}