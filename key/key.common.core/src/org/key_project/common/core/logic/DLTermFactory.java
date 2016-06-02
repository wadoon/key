package org.key_project.common.core.logic;

import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.common.core.logic.op.DLQuantifiableVariable;
import org.key_project.util.collection.ImmutableArray;

public interface DLTermFactory< S extends DLSort, 
                                T extends DLTerm<S, ? extends DLVisitor<T>>, 
                                O extends DLOperator,  
                                P extends Program,
                                Q extends DLQuantifiableVariable<S>> {

    /**
     * Master method for T creation. Should be the only place where terms 
     * are created in the entire system.
     */
    T createTerm(O op, ImmutableArray<T>  subs,
            ImmutableArray<Q> boundVars, 
            P program,
            ImmutableArray<TermLabel> labels);

    T createTerm(O op, ImmutableArray<T>  subs,
            ImmutableArray<Q> boundVars,
            P Program);

    T createTerm(O op, T[] subs,
            ImmutableArray<Q> boundVars,
            P Program);

    T createTerm(O op, @SuppressWarnings("unchecked") T... subs);

    T createTerm(O op, T[] subs,
            ImmutableArray<Q> boundVars, P program,
            ImmutableArray<TermLabel> labels);

    T createTerm(O op, T[] subs,
            ImmutableArray<Q> boundVars, P program,
            TermLabel label);

    T createTerm(O op, T[] subs, TermLabel label);

    T createTerm(O op, T[] subs, ImmutableArray<TermLabel> labels);

    T createTerm(O op, T sub, ImmutableArray<TermLabel> labels);

    T createTerm(O op, T sub1, T sub2,
            ImmutableArray<TermLabel> labels);

    T createTerm(O op, ImmutableArray<TermLabel> labels);

}