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
import java.util.HashMap;
import java.util.Set;
import java.util.WeakHashMap;

import de.uka.ilkd.key.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.ldt.SetLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.MiscTools;

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
    private final Set<Term> assignables;

    private AbstractUpdate(AbstractPlaceholderStatement phs, Term lhs,
            LocSetLDT locSetLDT, SetLDT setLDT) {
        super(new Name("U_" + phs.getId() + "(" + lhs + ")"),
                new Sort[] { setLDT.targetSort() }, Sort.UPDATE, false);
        this.lhs = lhs;
        this.assignables = MiscTools.dissasembleSetTerm(lhs,
                locSetLDT.getUnion());
        this.phs = phs;
        assert lhs.sort() == locSetLDT.targetSort();
    }

    /**
     * Returns the abstract update operator for the passed left hand side.
     */
    public static AbstractUpdate getInstance(AbstractPlaceholderStatement phs,
            Term lhs, LocSetLDT locSetLDT, SetLDT setLDT) {
        if (INSTANCES.get(phs) == null) {
            INSTANCES.put(phs, new WeakHashMap<>());
        }

        WeakReference<AbstractUpdate> result = INSTANCES.get(phs).get(lhs);
        if (result == null || result.get() == null) {
            result = new WeakReference<AbstractUpdate>(
                    new AbstractUpdate(phs, lhs, locSetLDT, setLDT));
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
    public Set<Term> getAssignables() {
        return assignables;
    }

    private static UnionTermHashMapKey key(Term lhs, LocSetLDT locSetLDT) {
        return new UnionTermHashMapKey(lhs, locSetLDT);
    }

    /**
     * A key class for use in a {@link HashMap} ensuring that {@link LocSetLDT}
     * union {@link Term}s get the same hash code whatever the order of elements
     * in the union is -- as it should be for a set union.
     */
    private static class UnionTermHashMapKey {
        private final int hashCode;
        private final Term lhs;

        public UnionTermHashMapKey(Term lhs, LocSetLDT locSetLDT) {
            /*
             * We also store the LHS because otherwise, these key objects are
             * removed when put into a weak reference, and that before they
             * should be.
             */
            this.lhs = lhs;
            this.hashCode = MiscTools
                    .dissasembleSetTerm(lhs, locSetLDT.getUnion()).hashCode();
        }

        @Override
        public int hashCode() {
            return hashCode;
        }

        @Override
        public boolean equals(Object obj) {
            return (obj instanceof UnionTermHashMapKey)
                    && ((UnionTermHashMapKey) obj).hashCode == hashCode;
        }
    }
}