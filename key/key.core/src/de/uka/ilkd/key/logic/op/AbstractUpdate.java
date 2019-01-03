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

package de.uka.ilkd.key.logic.op;

import java.lang.ref.WeakReference;
import java.util.LinkedList;
import java.util.List;
import java.util.WeakHashMap;

import de.uka.ilkd.key.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.ldt.LDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Class of operators for abstract updates (in the sense of Abstract Execution),
 * i.e., updates of the form "U(LOCSET1 := LOCSET2)", where LOCSET1/2 are
 * location sets. There is one such operator for every left hand side "LOCSET1".
 * Each of these operator is unary, accepting a single argument "LOCSET2".
 * Comparable to an {@link ElementaryUpdate}.
 */
public final class AbstractUpdate extends AbstractSortedOperator {

    private static final WeakHashMap<AbstractPlaceholderStatement, //
            WeakHashMap<Term, WeakReference<AbstractUpdate>>> INSTANCES = //
                    new WeakHashMap<>();

    private final AbstractPlaceholderStatement phs;
    private final Term lhs;
    private final List<Term> assignables;

    private AbstractUpdate(AbstractPlaceholderStatement phs, Term lhs,
            LocSetLDT locSetLDT) {
        super(new Name("U_" + phs.getId() + "(" + lhs + ")"),
                new Sort[] { lhs.sort() }, Sort.UPDATE, false);
        this.lhs = lhs;
        this.assignables = getUnionElements(lhs, locSetLDT);
        this.phs = phs;
        assert lhs.sort() == locSetLDT.targetSort();
    }

    /**
     * Returns the abstract update operator for the passed left hand side.
     */
    public static AbstractUpdate getInstance(AbstractPlaceholderStatement phs,
            Term lhs, LocSetLDT locSetLDT) {
        if (INSTANCES.get(phs) == null) {
            INSTANCES.put(phs, new WeakHashMap<>());
        }

        WeakReference<AbstractUpdate> result = INSTANCES.get(phs).get(lhs);
        if (result == null || result.get() == null) {
            result = new WeakReference<AbstractUpdate>(
                    new AbstractUpdate(phs, lhs, locSetLDT));
            INSTANCES.get(phs).put(lhs, result);
        }

        return result.get();
    }

    public AbstractPlaceholderStatement getAbstractPlaceholderStatement() {
        return this.phs;
    }

    /**
     * Returns the left hand side of this abstract update operator.
     */
    public Term lhs() {
        return this.lhs;
    }

    public String getUpdateName() {
        /*
         * TODO (DS, 2019-01-03): There might be collissions here, ignoring for
         * now...
         */
        return "U_" + phs.getId();
    }

    @Override
    public int hashCode() {
        return 5 + 17 * this.lhs.hashCode() + 27 * this.phs.hashCode();
    }

    /**
     * Retrieves the assignables of this abstract updates.
     *
     * @return The elements of the assignables union of this abstract update.
     */
    public List<Term> getAssignables() {
        return assignables;
    }

    /**
     * Retrieves the elements of a union and returns them as a list.
     *
     * @param t
     *            The term to disassemble.
     * @param locSetLDT
     *            The locset {@link LDT}.
     * @return The elements of the given union.
     */
    private static List<Term> getUnionElements(Term t, LocSetLDT locSetLDT) {
        final LinkedList<Term> result = new LinkedList<>();

        if (t.op() != locSetLDT.getUnion()) {
            result.add(t);
            return result;
        }
        else {
            result.addAll(getUnionElements(t.sub(0), locSetLDT));
            result.addAll(getUnionElements(t.sub(1), locSetLDT));
            return result;
        }
    }
}