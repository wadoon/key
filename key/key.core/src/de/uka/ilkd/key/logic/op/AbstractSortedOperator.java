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

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Sorted;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Abstract sorted operator class offering some common functionality.
 */
public abstract class AbstractSortedOperator extends
        GenericAbstractSortedOperator implements GenericSortedOperator, Sorted, ExtendedTypeCheckingAndInferenceService {

    protected AbstractSortedOperator(Name name, ImmutableArray<Sort> argSorts,
            Sort sort, ImmutableArray<Boolean> whereToBind, boolean isRigid) {
        super(name, argSorts, sort, whereToBind, isRigid);
    }

    protected AbstractSortedOperator(Name name, Sort[] argSorts, Sort sort,
            Boolean[] whereToBind, boolean isRigid) {
        this(name, new ImmutableArray<Sort>(argSorts), sort,
                new ImmutableArray<Boolean>(whereToBind), isRigid);
    }

    protected AbstractSortedOperator(Name name, ImmutableArray<Sort> argSorts,
            Sort sort, boolean isRigid) {
        this(name, argSorts, sort, null, isRigid);
    }

    protected AbstractSortedOperator(Name name, Sort[] argSorts, Sort sort,
            boolean isRigid) {
        this(name, new ImmutableArray<Sort>(argSorts), sort, null, isRigid);
    }

    protected AbstractSortedOperator(Name name, Sort sort, boolean isRigid) {
        this(name, (ImmutableArray<Sort>) null, sort, null, isRigid);
    }

    @Override
    public final Sort sort(ImmutableArray<Term> terms) {
        return sort;
    }

    /**
     * checks if a given Term could be subterm (at the at'th subterm position)
     * of a term with this function at its top level. The validity of the given
     * subterm is NOT checked.
     * 
     * @param at
     *            theposition of the term where this method should check the
     *            validity.
     * @param possibleSub
     *            the subterm to be ckecked.
     * @return true iff the given term can be subterm at the indicated position
     */
    private boolean possibleSub(int at, Term possibleSub) {
        final Sort s = possibleSub.sort();

        return s == AbstractTermTransformer.METASORT
                || s instanceof ProgramSVSort
                || argSort(at) == AbstractTermTransformer.METASORT
                || argSort(at) instanceof ProgramSVSort
                || s.extendsTrans(argSort(at));
    }

    /**
     * Allows subclasses to impose custom demands on what constitutes a valid
     * term using the operator represented by the subclass. The default
     * implementation here does not impose any such demands.
     */
    protected boolean additionalValidTopLevel2(Term term) {
        return true;
    }

    @Override
    public boolean additionalValidTopLevel(Term term) {
        for (int i = 0, n = arity(); i < n; i++) {
            if (!possibleSub(i, term.sub(i))) {
                return false;
            }
        }
        return additionalValidTopLevel2(term);
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.op.ExtendedTypeCheckingAndInferenceService#validTopLevel(de.uka.ilkd.key.logic.Term)
     */
    @Override
    public boolean validTopLevel(Term term) {
        if (arity != term.arity() || arity != term.subs().size()
                || (whereToBind == null) != term.boundVars().isEmpty()) {
            return false;
        }

        for (int i = 0, n = arity; i < n; i++) {
            if (term.sub(i) == null) {
                return false;
            }
        }

        return additionalValidTopLevel(term);
    }
}
