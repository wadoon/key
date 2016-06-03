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

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Sorted;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 */
public abstract class AbstractSortedOperator extends AbstractOperator
        implements SortedOperator, Sorted {

    protected static final ImmutableArray<Sort> EMPTY_SORT_LIST =
            new ImmutableArray<Sort>();
    protected final Sort sort;
    protected final ImmutableArray<Sort> argSorts;

    protected AbstractSortedOperator(Name name,
            ImmutableArray<Sort> argSorts, Sort sort,
            ImmutableArray<Boolean> whereToBind, boolean isRigid) {
        super(name, argSorts == null ? 0 : argSorts.size(), whereToBind,
                isRigid);
        assert sort != null;
        this.argSorts = argSorts == null ? EMPTY_SORT_LIST : argSorts;
        this.sort = sort;
    }

    protected AbstractSortedOperator(Name name, Sort[] argSorts,
            Sort sort, Boolean[] whereToBind, boolean isRigid) {
        this(name, new ImmutableArray<Sort>(argSorts), sort,
                new ImmutableArray<Boolean>(whereToBind), isRigid);
    }

    protected AbstractSortedOperator(Name name,
            ImmutableArray<Sort> argSorts, Sort sort, boolean isRigid) {
        this(name, argSorts, sort, null, isRigid);
    }

    protected AbstractSortedOperator(Name name, Sort[] argSorts,
            Sort sort, boolean isRigid) {
        this(name, new ImmutableArray<Sort>(argSorts), sort, null, isRigid);
    }

    protected AbstractSortedOperator(Name name, Sort sort,
            boolean isRigid) {
        this(name, (ImmutableArray<Sort>) null, sort, null, isRigid);
    }

    @Override
    public final Sort argSort(int i) {
        return argSorts.get(i);
    }

    @Override
    public final ImmutableArray<Sort> argSorts() {
        return argSorts;
    }

    @Override
    public final Sort sort() {
        return sort;
    }

}