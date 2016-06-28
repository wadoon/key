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

package org.key_project.common.core.logic.factories;

import java.lang.reflect.Array;
import java.util.Map;

import org.key_project.common.core.logic.CCTerm;
import org.key_project.common.core.logic.ModalContent;
import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.op.TypeCheckingAndInferenceService;
import org.key_project.util.collection.ImmutableArray;

/**
 * The TermFactory is the <em>only</em> way to create terms using constructors
 * of class Term or any of its subclasses. It is the only class that implements
 * and may exploit knowledge about sub classes of {@link CCTerm}. All other
 * classes of the system only know about terms what the {@link CCTerm} class
 * offers them.
 * 
 * This class is used to encapsulate knowledge about the internal term
 * structures. See {@link TermBuilder} for more convenient methods to create
 * terms.
 *
 * @author Dominic Scheurer
 */
public abstract class CCTermFactoryImpl<P extends ModalContent<?>, T extends CCTerm<?, P, ?, T>>
        implements CCTermFactory<P, T> {

    protected final Map<T, T> cache;
    
    private final Class<T> clazz;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public CCTermFactoryImpl(Map<T, T> cache, Class<T> clazz) {
        this.cache = cache;
        this.clazz = clazz;
    }

    protected abstract T doCreateTerm(Operator op, ImmutableArray<T> subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            P javaBlock, ImmutableArray<TermLabel> labels);

    // Helper methods for generic array creation
    
    @SuppressWarnings("unchecked")
    T[] createTermArray(int size) {
        return (T[]) Array.newInstance(clazz, size);
    }
    
    T[] createTermArray(T sub1) {
        T[] arr = createTermArray(1);
        arr[0] = sub1;
        return arr;
    }
    
    T[] createTermArray(T sub1, T sub2) {
        T[] arr = createTermArray(2);
        arr[0] = sub1;
        arr[1] = sub2;
        return arr;
    }
    
    T[] createTermArray(T sub1, T sub2, T sub3) {
        T[] arr = createTermArray(3);
        arr[0] = sub1;
        arr[1] = sub2;
        arr[2] = sub3;
        return arr;
    }

    protected abstract <O extends Operator> TypeCheckingAndInferenceService<O> getTypeCheckingAndInferenceService(
            O op);

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    /**
     * Master method for term creation. Should be the only place where terms are
     * created in the entire system.
     */
    @Override
    public T createTerm(Operator op, ImmutableArray<T> subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            P javaBlock, ImmutableArray<TermLabel> labels) {
        if (op == null) {
            throw new TermCreationException(
                    "null-Operator at GenericTermFactory");
        }

        if (subs == null || subs.isEmpty()) {
            subs = emptyTermList();
        }

        return cacheTerm(doCreateTerm(op, subs, boundVars, javaBlock, labels));
    }

    @Override
    public T createTerm(Operator op, ImmutableArray<T> subs,
            ImmutableArray<QuantifiableVariable> boundVars, P javaBlock) {

        return createTerm(op, subs, boundVars, javaBlock, null);
    }

    @Override
    public T createTerm(Operator op, T[] subs,
            ImmutableArray<QuantifiableVariable> boundVars, P javaBlock) {
        return createTerm(op, createSubtermArray(subs), boundVars, javaBlock,
                null);
    }

    @SafeVarargs
    @Override
    public final T createTerm(Operator op, T... subs) {
        return createTerm(op, subs, null, null);
    }

    @Override
    public T createTerm(Operator op, T[] subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            P javaBlock, ImmutableArray<TermLabel> labels) {
        return createTerm(op, createSubtermArray(subs), boundVars, javaBlock,
                labels);
    }

    @Override
    public T createTerm(Operator op, T[] subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            P javaBlock, TermLabel label) {
        return createTerm(op, createSubtermArray(subs), boundVars,
                javaBlock, new ImmutableArray<TermLabel>(label));
    }

    @Override
    public T createTerm(Operator op, T[] subs, TermLabel label) {
        return createTerm(op, subs, null, null, label);
    }

    @Override
    public T createTerm(Operator op, T[] subs, ImmutableArray<TermLabel> labels) {
        return createTerm(op, createSubtermArray(subs), null, null, labels);
    }

    @Override
    public T createTerm(Operator op, T sub, ImmutableArray<TermLabel> labels) {
        return createTerm(op, new ImmutableArray<T>(sub), null, null, labels);
    }

    @Override
    public T createTerm(Operator op, T sub1, T sub2,
            ImmutableArray<TermLabel> labels) {
        return createTerm(op, createTermArray(sub1, sub2), null, null, labels);
    }

    @Override
    public T createTerm(Operator op, ImmutableArray<TermLabel> labels) {
        return createTerm(op, emptyTermList(), null, null, labels);
    }

    // -------------------------------------------------------------------------
    // protected interface
    // -------------------------------------------------------------------------

    /**
     * Checks whether the T is valid on the top level. If this is the case this
     * method returns the T unmodified. Otherwise a TermCreationException is
     * thrown.
     * 
     * @param term
     *            the {@link T} to be checked
     * @return the same term
     * @throws TermCreationException
     *             if the term is not wellformed
     */
    protected final T checked(T term) {
        final Operator op = term.op();
        if (getTypeCheckingAndInferenceService(op)
                .validTopLevel(term, op)) {
            return term;
        }
        else {
            throw new TermCreationException(op, term,
                    getTypeCheckingAndInferenceService(op)
                            .sort(term.subs(), op));
        }
    }

    // -------------------------------------------------------------------------
    // private methods
    // -------------------------------------------------------------------------

    private ImmutableArray<T> createSubtermArray(T[] subs) {
        return subs == null || subs.length == 0 ?
                emptyTermList() : new ImmutableArray<T>(subs);
    }

    private ImmutableArray<T> emptyTermList() {
        return new ImmutableArray<T>(createTermArray(0));
    }

    private T cacheTerm(final T newTerm) {
        // Check if caching is possible. It is not possible if a non empty
        // P is available in the term or in one of its children because
        // the meta information like PositionInfos may be different.
        if (!newTerm.containsModalContentRecursive()) {

            T term;
            synchronized (cache) {
                term = cache.get(newTerm);
            }
            if (term == null) {
                term = checked(newTerm);
                synchronized (cache) {
                    cache.put(term, term);
                }
            }
            return term;
        }
        else {
            return checked(newTerm);
        }
    }

}