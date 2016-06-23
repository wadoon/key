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

import org.key_project.common.core.logic.CCTerm;
import org.key_project.common.core.logic.ModalContent;
import org.key_project.common.core.logic.UpdateLabelPair;
import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.common.core.logic.op.*;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 * @param <P>
 * @param <T>
 */
public interface CCTermBuilder<P extends ModalContent, T extends CCTerm<P, ?, T>> {

    CCTermFactoryImpl<P, T> tf();

    String shortBaseName(Sort s);

    T var(LogicVariable v);

    T var(CCProgramVariable v);

    ImmutableList<T> var(CCProgramVariable... vs);

    ImmutableList<T> var(Iterable<? extends CCProgramVariable> vs);

    T var(SchemaVariable v);

    T var(ParsableVariable v);

    T func(Function f);

    T func(Function f, T s);

    T func(Function f, T s1, T s2);

    T func(Function f, @SuppressWarnings("unchecked") T... s);

    T func(Function f,
            T[] s,
            ImmutableArray<QuantifiableVariable> boundVars);

    T prog(Modality mod, P jb, T t);

    T prog(Modality mod, P jb, T t, ImmutableArray<TermLabel> labels);

    T box(P jb, T t);

    T dia(P jb, T t);

    T ife(T cond, T _then, T _else);

    /** Construct a term with the \ifEx operator. */
    T ifEx(QuantifiableVariable qv, T cond, T _then, T _else);

    /** Construct a term with the \ifEx operator. */
    T ifEx(ImmutableList<QuantifiableVariable> qvs, T cond, T _then,
            T _else);

    T tt();

    T ff();

    T all(QuantifiableVariable qv, T t);

    T all(Iterable<QuantifiableVariable> qvs, T t);

    T allClose(T t);

    /**
     * Removes universal quantifiers from a formula.
     */
    T open(T formula);

    T ex(QuantifiableVariable qv, T t);

    T ex(Iterable<QuantifiableVariable> qvs, T t);

    T not(T t);

    T and(T t1, T t2);

    T andSC(T t1, T t2);

    T and(@SuppressWarnings("unchecked") T... subTerms);

    T andSC(@SuppressWarnings("unchecked") T... subTerms);

    T and(Iterable<T> subTerms);

    T andSC(Iterable<T> subTerms);

    T or(T t1, T t2);

    T orSC(T t1, T t2);

    T or(@SuppressWarnings("unchecked") T... subTerms);

    T orSC(@SuppressWarnings("unchecked") T... subTerms);

    T or(Iterable<T> subTerms);

    T orSC(Iterable<T> subTerms);

    T imp(T t1, T t2);

    T imp(T t1, T t2, ImmutableArray<TermLabel> labels);

    /**
     * Creates a term with the correct equality symbol for the sorts involved
     */
    T equals(T t1, T t2);

    /**
     * Creates a substitution term
     * 
     * @param substVar
     *            the QuantifiableVariable to be substituted
     * @param substTerm
     *            the T that replaces substVar
     * @param origTerm
     *            the T that is substituted
     */
    T subst(CCSubstOp<?, T> op,
            QuantifiableVariable substVar,
            T substTerm,
            T origTerm);

    T subst(QuantifiableVariable substVar,
            T substTerm,
            T origTerm);

    T pair(T first, T second);

    T prec(T mby, T mbyAtPre);

    T measuredByCheck(T mby);

    T measuredBy(T mby);

    Function getMeasuredByEmpty();

    T measuredByEmpty();

    T elementary(UpdateableOperator lhs, T rhs);

    T skip();

    T parallel(T u1, T u2);

    T parallel(@SuppressWarnings("unchecked") T... updates);

    T parallel(ImmutableList<T> updates);

    T sequential(T u1, T u2);

    T sequential(T[] updates);

    T sequential(ImmutableList<T> updates);

    T apply(T update, T target);

    ImmutableList<T> apply(T update,
            ImmutableList<T> targets);

    T apply(T update, T target, ImmutableArray<TermLabel> labels);

    T applyParallel(T[] updates, T target);

    T applyParallel(ImmutableList<T> updates, T target);

    T applySequential(T[] updates, T target);

    T applySequential(ImmutableList<T> updates, T target);

    T applyUpdatePairsSequential(ImmutableList<UpdateLabelPair<T>> updates,
            T target);

    /**
     * This value is only used as a marker for "\strictly_nothing" in JML. It
     * may return any term. Preferably of type LocSet, but this is not
     * necessary.
     *
     * @return an arbitrary but fixed term.
     */
    T strictlyNothing();

    T addLabel(T term, ImmutableArray<TermLabel> labels);

    T addLabel(T term, TermLabel label);

    T label(T term, ImmutableArray<TermLabel> labels);

    T label(T term, TermLabel label);

    T shortcut(T term);

    T unlabel(T term);

    T unlabelRecursive(T term);

    /**
     * Returns the {@link Sort}s of the given {@link T}s.
     * 
     * @param terms
     *            The given {@link T}s.
     * @return The {@link T} {@link Sort}s.
     */
    ImmutableList<Sort> getSorts(Iterable<T> terms);

    /**
     * Similar behavior as {@link #imp(T, T)} but simplifications are not
     * performed if {@link TermLabel}s would be lost.
     * 
     * @param t1
     *            The left side.
     * @param t2
     *            The right side.
     * @return The created {@link T}.
     */
    T impPreserveLabels(T t1, T t2);

    /**
     * Similar behavior as {@link #not(T)} but simplifications are not performed
     * if {@link TermLabel}s would be lost.
     * 
     * @param t
     *            The child {@link T}.
     * @return The created {@link T}.
     */
    T notPreserveLabels(T t);

    /**
     * Similar behavior as {@link #and(Iterable)} but simplifications are not
     * performed if {@link TermLabel}s would be lost.
     * 
     * @param subTerms
     *            The sub {@link T}s.
     * @return The created {@link T}.
     */
    T andPreserveLabels(Iterable<T> subTerms);

    /**
     * Similar behavior as {@link #and(T, T)} but simplifications are not
     * performed if {@link TermLabel}s would be lost.
     * 
     * @param t1
     *            The left side.
     * @param t2
     *            The right side.
     * @return The created {@link T}.
     */
    T andPreserveLabels(T t1, T t2);

    /**
     * Similar behavior as {@link #or(Iterable)} but simplifications are not
     * performed if {@link TermLabel}s would be lost.
     * 
     * @param subTerms
     *            The sub {@link T}s.
     * @return The created {@link T}.
     */
    T orPreserveLabels(Iterable<T> subTerms);

    /**
     * Similar behavior as {@link #or(T, T)} but simplifications are not
     * performed if {@link TermLabel}s would be lost.
     * 
     * @param t1
     *            The left side.
     * @param t2
     *            The right side.
     * @return The created {@link T}.
     */
    T orPreserveLabels(T t1, T t2);

}