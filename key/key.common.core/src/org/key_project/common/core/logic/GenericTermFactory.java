package org.key_project.common.core.logic;

import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.program.GenericNameAbstractionTable;
import org.key_project.util.collection.ImmutableArray;

public interface GenericTermFactory<S, T extends GenericTerm<S, T, V, N>, V extends Visitor<S, V, T, N>, N extends GenericNameAbstractionTable<S>, P extends ModalContent<S, N>> {
    
    /**
     * Master method for term creation. Should be the only place where terms are
     * created in the entire system.
     */
    public T createTerm(Operator op, ImmutableArray<T> subs,
            ImmutableArray<QuantifiableVariable> boundVars, P javaBlock,
            ImmutableArray<TermLabel> labels);

    public T createTerm(Operator op, ImmutableArray<T> subs,
            ImmutableArray<QuantifiableVariable> boundVars, P javaBlock);

    public T createTerm(Operator op, T[] subs,
            ImmutableArray<QuantifiableVariable> boundVars, P javaBlock);

    public T createTerm(Operator op, @SuppressWarnings("unchecked") T... subs);

    public T createTerm(Operator op, T[] subs,
            ImmutableArray<QuantifiableVariable> boundVars, P javaBlock,
            ImmutableArray<TermLabel> labels);

    public T createTerm(Operator op, T[] subs,
            ImmutableArray<QuantifiableVariable> boundVars, P javaBlock,
            TermLabel label);

    public T createTerm(Operator op, T[] subs, TermLabel label);

    public T createTerm(Operator op, T[] subs, ImmutableArray<TermLabel> labels);

    public T createTerm(Operator op, T sub, ImmutableArray<TermLabel> labels);

    public T createTerm(Operator op, T sub1, T sub2,
            ImmutableArray<TermLabel> labels);

    public T createTerm(Operator op, ImmutableArray<TermLabel> labels);
}
