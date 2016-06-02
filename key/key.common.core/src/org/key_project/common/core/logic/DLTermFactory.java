package org.key_project.common.core.logic;

import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.util.collection.ImmutableArray;

public interface DLTermFactory< T extends DLTerm<? extends DLVisitor<T>>,                                 
                                P extends Program> {

    /**
     * Master method for T creation. Should be the only place where terms 
     * are created in the entire system.
     */
    T createTerm(Operator op, ImmutableArray<T>  subs,
            ImmutableArray<QuantifiableVariable> boundVars, 
            P program,
            ImmutableArray<TermLabel> labels);

    T createTerm(Operator op, ImmutableArray<T>  subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            P Program);

    T createTerm(Operator op, T[] subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            P Program);

    T createTerm(Operator op, @SuppressWarnings("unchecked") T... subs);

    T createTerm(Operator op, T[] subs,
            ImmutableArray<QuantifiableVariable> boundVars, P program,
            ImmutableArray<TermLabel> labels);

    T createTerm(Operator op, T[] subs,
            ImmutableArray<QuantifiableVariable> boundVars, P program,
            TermLabel label);

    T createTerm(Operator op, T[] subs, TermLabel label);

    T createTerm(Operator op, T[] subs, ImmutableArray<TermLabel> labels);

    T createTerm(Operator op, T sub, ImmutableArray<TermLabel> labels);

    T createTerm(Operator op, T sub1, T sub2,
            ImmutableArray<TermLabel> labels);

    T createTerm(Operator op, ImmutableArray<TermLabel> labels);

}