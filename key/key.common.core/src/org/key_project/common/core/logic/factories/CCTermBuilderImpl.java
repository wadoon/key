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

package org.key_project.common.core.logic.factories;

import java.util.ArrayList;

import org.key_project.common.core.logic.*;
import org.key_project.common.core.logic.label.ParameterlessTermLabel;
import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.common.core.logic.op.*;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.services.TermServices;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.Pair;

/**
 * <p>
 * Use this class if you intend to build complex terms by hand. It is more
 * convenient than the @link{GenericTermFactory} class.
 * </p>
 *
 * <p>
 * Attention: some methods of this class try to simplify some terms. So if you
 * want to be sure that the term looks exactly as you built it, you will have to
 * use the GenericTermFactory.
 * </p>
 */
public abstract class CCTermBuilderImpl<P extends ModalContent, T extends CCTerm<?, T>>
        implements CCTermBuilder<P, T> {

    private final CCTermFactoryImpl<P, T> tf;
    private final T tt;
    private final T ff;
    
    private final TermServices services;

    public CCTermBuilderImpl(CCTermFactoryImpl<P, T> tf, TermServices services) {
        this.services = services;
        this.tf = tf;
        this.tt = tf.createTerm(Junctor.TRUE);
        this.ff = tf.createTerm(Junctor.FALSE);
    }

    @Override
    public CCTermFactoryImpl<P, T> tf() {
        return tf;
    }

    // -------------------------------------------------------------------------
    // naming
    // -------------------------------------------------------------------------

    @Override
    public String shortBaseName(Sort s) {
        String result = s.name().toString();
        int index = result.lastIndexOf(".");
        if (index == -1) {
            result = result.charAt(0) + "";
        }
        else {
            result = result.substring(index).charAt(1) + "";
        }
        return result.toLowerCase();
    }

    // -------------------------------------------------------------------------
    // common variable constructions
    // -------------------------------------------------------------------------

    // -------------------------------------------------------------------------
    // constructors for special classes of term operators
    // -------------------------------------------------------------------------

    @Override
    public T var(LogicVariable v) {
        return tf.createTerm(v);
    }

    @Override
    public T var(CCProgramVariable v) {
        // if(v.isMember()) {
        // throw new TermCreationException(
        // "Cannot create term for \"member\" "
        // + "program variable \"" + v + "\". Use field symbols "
        // + "like your mother told you!");
        // }
        return tf.createTerm(v);
    }

    @Override
    public ImmutableList<T> var(CCProgramVariable... vs) {
        ImmutableList<T> result = ImmutableSLList.<T> nil();
        for (CCProgramVariable v : vs) {
            result = result.append(var(v));
        }
        return result;
    }

    @Override
    public ImmutableList<T> var(Iterable<? extends CCProgramVariable> vs) {
        ImmutableList<T> result = ImmutableSLList.<T> nil();
        for (CCProgramVariable v : vs) {
            result = result.append(var(v));
        }
        return result;
    }

    @Override
    public T var(SchemaVariable v) {
        return tf.createTerm(v);
    }

    @Override
    public T var(ParsableVariable v) {
        return tf.createTerm(v);
    }

    @Override
    public T func(Function f) {
        return tf.createTerm(f);
    }

    @Override
    public T func(Function f, T s) {
        return tf.createTerm(f, s);
    }

    @Override
    public T func(Function f, T s1, T s2) {
        return tf.createTerm(f, s1, s2);
    }

    @Override
    public T func(Function f, @SuppressWarnings("unchecked") T... s) {
        return tf.createTerm(f, s, null, null);
    }

    @Override
    public T func(Function f,
            T[] s,
            ImmutableArray<QuantifiableVariable> boundVars) {
        return tf.createTerm(f, s, boundVars, null);
    }

    @Override
    public T prog(Modality mod, P jb, T t) {
        return tf.createTerm(mod, tf.createTermArray(t), null, jb);
    }

    @Override
    public T prog(Modality mod, P jb, T t, ImmutableArray<TermLabel> labels) {
        return tf.createTerm(mod, tf.createTermArray(t), null, jb, labels);
    }

    @Override
    public T box(P jb, T t) {
        return prog(Modality.BOX, jb, t);
    }

    @Override
    public T dia(P jb, T t) {
        return prog(Modality.DIA, jb, t);
    }

    @Override
    public T ife(T cond, T _then, T _else) {
        return tf.createTerm(IfThenElse.IF_THEN_ELSE,
                tf.createTermArray(cond, _then, _else));
    }

    @Override
    public T ifEx(QuantifiableVariable qv, T cond, T _then, T _else) {
        return tf.createTerm(IfExThenElse.IF_EX_THEN_ELSE,
                new ImmutableArray<T>(cond, _then, _else),
                new ImmutableArray<QuantifiableVariable>(qv),
                null);
    }

    @Override
    public T ifEx(ImmutableList<QuantifiableVariable> qvs, T cond, T _then,
            T _else) {
        if (qvs.isEmpty())
            throw new TermCreationException(
                    "no quantifiable variables in ifEx term");
        if (qvs.size() == 1) {
            return ifEx(qvs.head(), cond, _then, _else);
        }
        else {
            return ifEx(qvs.head(), tt(), ifEx(qvs.tail(), cond, _then, _else),
                    _else);
        }
    }

    @Override
    public T tt() {
        return tt;
    }

    @Override
    public T ff() {
        return ff;
    }

    @Override
    public T all(QuantifiableVariable qv, T t) {
        return tf.createTerm(Quantifier.ALL,
                new ImmutableArray<T>(t),
                new ImmutableArray<QuantifiableVariable>(qv),
                null);
    }

    @Override
    public T all(Iterable<QuantifiableVariable> qvs, T t) {
        T result = t;
        for (QuantifiableVariable fv : qvs) {
            result = all(fv, result);
        }
        return result;
    }

    @Override
    public T allClose(T t) {
        return all(t.freeVars(), t);
    }

    @Override
    public T open(T formula) {
        assert formula.sort() == Sort.FORMULA;
        if (formula.op() == Quantifier.ALL) {
            return open(formula.sub(0));
        }
        else {
            return formula;
        }
    }

    @Override
    public T ex(QuantifiableVariable qv, T t) {
        return tf.createTerm(Quantifier.EX,
                new ImmutableArray<T>(t),
                new ImmutableArray<QuantifiableVariable>(qv),
                null);
    }

    @Override
    public T ex(Iterable<QuantifiableVariable> qvs, T t) {
        T result = t;
        for (QuantifiableVariable fv : qvs) {
            result = ex(fv, result);
        }
        return result;
    }

    @Override
    public T not(T t) {
        if (t.op() == Junctor.TRUE) {
            return ff();
        }
        else if (t.op() == Junctor.FALSE) {
            return tt();
        }
        else if (t.op() == Junctor.NOT) {
            return t.sub(0);
        }
        else {
            return tf.createTerm(Junctor.NOT, t);
        }
    }

    @Override
    public T and(T t1, T t2) {
        if (t1.op() == Junctor.FALSE || t2.op() == Junctor.FALSE) {
            return ff();
        }
        else if (t1.op() == Junctor.TRUE) {
            return t2;
        }
        else if (t2.op() == Junctor.TRUE) {
            return t1;
        }
        else {
            return tf.createTerm(Junctor.AND, t1, t2);
        }
    }

    @Override
    public T andSC(T t1, T t2) {
        if (t1.op() == Junctor.TRUE || t1.op() == Junctor.FALSE
                || t2.op() == Junctor.FALSE || t2.op() == Junctor.TRUE) {
            return and(t1, t2);
        }
        else {
            return shortcut(and(t1, t2));
        }
    }

    @Override
    public T and(@SuppressWarnings("unchecked") T... subTerms) {
        T result = tt();
        for (T sub : subTerms) {
            result = and(result, sub);
        }
        return result;
    }

    @Override
    public T andSC(@SuppressWarnings("unchecked") T... subTerms) {
        T result = tt();
        if (subTerms.length == 1) {
            return and(subTerms);
        }
        for (T sub : subTerms) {
            result = andSC(result, sub);
        }
        return result;
    }

    @Override
    public T and(Iterable<T> subTerms) {
        T result = tt();
        for (T sub : subTerms) {
            result = and(result, sub);
        }
        return result;
    }

    @Override
    public T andSC(Iterable<T> subTerms) {
        T result = tt();
        int i = 0;
        for (T sub : subTerms) {
            result = andSC(result, sub);
            i++;
        }
        if (i == 1) {
            return and(subTerms);
        }
        return result;
    }

    @Override
    public T or(T t1, T t2) {
        if (t1.op() == Junctor.TRUE || t2.op() == Junctor.TRUE) {
            return tt();
        }
        else if (t1.op() == Junctor.FALSE) {
            return t2;
        }
        else if (t2.op() == Junctor.FALSE) {
            return t1;
        }
        else {
            return tf.createTerm(Junctor.OR, t1, t2);
        }
    }

    @Override
    public T orSC(T t1, T t2) {
        if (t1.op() == Junctor.TRUE || t1.op() == Junctor.FALSE
                || t2.op() == Junctor.FALSE || t2.op() == Junctor.TRUE) {
            return or(t1, t2);
        }
        else {
            return shortcut(or(t1, t2));
        }
    }

    @Override
    public T or(@SuppressWarnings("unchecked") T... subTerms) {
        T result = ff();
        for (T sub : subTerms) {
            result = or(result, sub);
        }
        return result;
    }

    @Override
    public T orSC(@SuppressWarnings("unchecked") T... subTerms) {
        T result = ff();
        if (subTerms.length == 1) {
            return or(subTerms);
        }
        for (T sub : subTerms) {
            result = orSC(result, sub);
        }
        return result;
    }

    @Override
    public T or(Iterable<T> subTerms) {
        T result = ff();
        for (T sub : subTerms) {
            result = or(result, sub);
        }
        return result;
    }

    @Override
    public T orSC(Iterable<T> subTerms) {
        T result = ff();
        int i = 0;
        for (T sub : subTerms) {
            result = orSC(result, sub);
            i++;
        }
        if (i == 1) {
            return or(subTerms);
        }
        return result;
    }

    @Override
    public T imp(T t1, T t2) {
        return imp(t1, t2, null);
    }

    @Override
    public T imp(T t1, T t2, ImmutableArray<TermLabel> labels) {
        if (t1.op() == Junctor.FALSE || t2.op() == Junctor.TRUE) {
            return tt();
        }
        else if (t1.op() == Junctor.TRUE) {
            return t2;
        }
        else if (t2.op() == Junctor.FALSE) {
            return not(t1);
        }
        else {
            return tf.createTerm(Junctor.IMP, t1, t2, labels);
        }
    }

    @Override
    public T equals(T t1, T t2) {
        if (t1.sort() == Sort.FORMULA) {
            if (t1.op() == Junctor.TRUE) {
                return t2;
            }
            else if (t2.op() == Junctor.TRUE) {
                return t1;
            }
            else if (t1.op() == Junctor.FALSE) {
                return not(t2);
            }
            else if (t2.op() == Junctor.FALSE) {
                return not(t1);
            }
            else {
                return tf.createTerm(Equality.EQV, t1, t2);
            }
        }
        else {
            return tf.createTerm(Equality.EQUALS, t1, t2);
        }
    }

    @Override
    public T subst(CCSubstOp<T> op,
            QuantifiableVariable substVar,
            T substTerm,
            T origTerm) {
        return tf.createTerm(op,
                new ImmutableArray<T>(tf.createTermArray(substTerm, origTerm)),
                new ImmutableArray<QuantifiableVariable>(substVar),
                null);
    }

    @Override
    public T subst(QuantifiableVariable substVar,
            T substTerm,
            T origTerm) {
        return subst(substOp(),
                substVar,
                substTerm,
                origTerm);
    }

    /**
     * @return The standard substitution operator, currently WarySubstOp.
     */
    protected abstract CCSubstOp<T> substOp();

    // Functions for wellfoundedness
    // ------------------------------

    @Override
    public T pair(T first, T second) {
        final Namespace funcNS = services.getNamespaces().functions();
        final Function f = (Function) funcNS.lookup(new Name("pair"));
        if (f == null)
            throw new RuntimeException(
                    "LDT: Function pair not found.\n"
                            +
                            "It seems that there are definitions missing from the .key files.");

        return func(f, first, second);

    }

    @Override
    public T prec(T mby, T mbyAtPre) {
        final Namespace funcNS = services.getNamespaces().functions();
        final Function f = (Function) funcNS.lookup(new Name("prec"));
        if (f == null)
            throw new RuntimeException(
                    "LDT: Function prec not found.\n"
                            +
                            "It seems that there are definitions missing from the .key files.");

        return func(f, mby, mbyAtPre);
    }

    @Override
    public T measuredByCheck(T mby) {
        final Namespace funcNS = services.getNamespaces().functions();
        final Function f =
                (Function) funcNS.lookup(new Name("measuredByCheck"));
        if (f == null)
            throw new RuntimeException(
                    "LDT: Function measuredByCheck not found.\n"
                            +
                            "It seems that there are definitions missing from the .key files.");
        return func(f, mby);
    }

    @Override
    public T measuredBy(T mby) {
        final Namespace funcNS = services.getNamespaces().functions();
        final Function f = (Function) funcNS.lookup(new Name("measuredBy"));
        if (f == null)
            throw new RuntimeException(
                    "LDT: Function measuredBy not found.\n"
                            +
                            "It seems that there are definitions missing from the .key files.");
        return func(f, mby);
    }

    @Override
    public Function getMeasuredByEmpty() {
        final Namespace funcNS = services.getNamespaces().functions();
        final Function f =
                (Function) funcNS.lookup(new Name("measuredByEmpty"));
        if (f == null)
            throw new RuntimeException(
                    "LDT: Function measuredByEmpty not found.\n"
                            +
                            "It seems that there are definitions missing from the .key files.");
        return f;
    }

    @Override
    public T measuredByEmpty() {
        return func(getMeasuredByEmpty());
    }

    // -------------------------------------------------------------------------
    // updates
    // -------------------------------------------------------------------------

    @Override
    public T elementary(UpdateableOperator lhs, T rhs) {
        ElementaryUpdate eu = ElementaryUpdate.getInstance(lhs);
        return tf.createTerm(eu, rhs);
    }

    @Override
    public T skip() {
        return tf.createTerm(UpdateJunctor.SKIP);
    }

    @Override
    public T parallel(T u1, T u2) {
        if (u1.sort() != Sort.UPDATE) {
            throw new TermCreationException("Not an update: " + u1);
        }
        else if (u2.sort() != Sort.UPDATE) {
            throw new TermCreationException("Not an update: " + u2);
        }
        if (u1.op() == UpdateJunctor.SKIP) {
            return u2;
        }
        else if (u2.op() == UpdateJunctor.SKIP) {
            return u1;
        }
        return tf.createTerm(UpdateJunctor.PARALLEL_UPDATE, u1, u2);
    }

    @Override
    public T parallel(@SuppressWarnings("unchecked") T... updates) {
        T result = skip();
        for (int i = 0; i < updates.length; i++) {
            result = parallel(result, updates[i]);
        }
        return result;
    }

    @Override
    public T parallel(ImmutableList<T> updates) {
        return parallel(updates.toArray(tf.createTermArray(updates.size())));
    }

    @Override
    public T sequential(T u1, T u2) {
        return parallel(u1, apply(u1, u2, null));
    }

    @Override
    public T sequential(T[] updates) {
        if (updates.length == 0) {
            return skip();
        }
        else {
            T result = updates[updates.length - 1];
            for (int i = updates.length - 2; i >= 0; i++) {
                result = sequential(updates[i], result);
            }
            return result;
        }
    }

    @Override
    public T sequential(ImmutableList<T> updates) {
        if (updates.isEmpty()) {
            return skip();
        }
        else if (updates.size() == 1) {
            return updates.head();
        }
        else {
            return sequential(updates.head(), sequential(updates.tail()));
        }
    }

    @Override
    public T apply(T update, T target) {
        return apply(update, target, null);
    }

    @Override
    public ImmutableList<T> apply(T update,
            ImmutableList<T> targets) {
        ImmutableList<T> result = ImmutableSLList.<T> nil();
        for (T target : targets) {
            result = result.append(apply(update, target));
        }
        return result;
    }

    @Override
    public T apply(T update, T target, ImmutableArray<TermLabel> labels) {
        if (update.sort() != Sort.UPDATE) {
            throw new TermCreationException("Not an update: " + update);
        }
        else if (update.op() == UpdateJunctor.SKIP) {
            return target;
        }
        else if (target.equals(tt())) {
            return tt();
        }
        else {
            return tf.createTerm(UpdateApplication.UPDATE_APPLICATION,
                    update,
                    target,
                    labels);
        }
    }

    @Override
    public T applyParallel(T[] updates, T target) {
        return apply(parallel(updates), target, null);
    }

    @Override
    public T applyParallel(ImmutableList<T> updates, T target) {
        return apply(parallel(updates), target, null);
    }

    @Override
    public T applySequential(T[] updates, T target) {
        if (updates.length == 0) {
            return target;
        }
        else {
            ImmutableList<T> updateList = ImmutableSLList.<T> nil()
                    .append(updates)
                    .tail();
            return apply(updates[0],
                    applySequential(updateList, target), null);
        }
    }

    @Override
    public T applySequential(ImmutableList<T> updates, T target) {
        if (updates.isEmpty()) {
            return target;
        }
        else {
            return apply(updates.head(),
                    applySequential(updates.tail(), target), null);
        }
    }

    @Override
    public T applyUpdatePairsSequential(
            ImmutableList<UpdateLabelPair<T>> updates,
            T target) {
        if (updates.isEmpty()) {
            return target;
        }
        else {
            return apply(updates.head().getUpdate(),
                    applyUpdatePairsSequential(updates.tail(), target), updates
                            .head().getUpdateApplicationlabels());
        }
    }

    // -------------------------------------------------------------------------
    // location set operators
    // -------------------------------------------------------------------------

    @Override
    public T strictlyNothing() {
        return ff();
    }

    @Override
    public T addLabel(T term, ImmutableArray<TermLabel> labels) {
        if ((labels == null || labels.isEmpty())
                && !term.hasLabels()) {
            return term;
        }
        else if (!term.hasLabels()) {
            return tf.createTerm(term.op(), term.subs(), term.boundVars(),
                    term.<P> modalContent(), labels);
        }
        else {
            ArrayList<TermLabel> newLabelList = new ArrayList<TermLabel>();
            for (TermLabel l : term.getLabels()) {
                newLabelList.add(l);
            }
            for (TermLabel l : labels) {
                if (!newLabelList.contains(l)) {
                    newLabelList.add(l);
                }
            }
            return tf.createTerm(term.op(), term.subs(),
                    term.boundVars(), term.<P> modalContent(),
                    new ImmutableArray<TermLabel>(newLabelList));
        }
    }

    @Override
    public T addLabel(T term, TermLabel label) {
        if (label == null && !term.hasLabels()) {
            return term;
        }
        else {
            return addLabel(term, new ImmutableArray<TermLabel>(label));
        }
    }

    @Override
    public T label(T term, ImmutableArray<TermLabel> labels) {
        if ((labels == null || labels.isEmpty())) {
            return term;
        }
        else if (labels.size() == 1
                && (labels
                        .contains(ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL)
                        || labels
                                .contains(ParameterlessTermLabel.SHORTCUT_EVALUATION_LABEL)
                        || labels
                            .contains(ParameterlessTermLabel.UNDEFINED_VALUE_LABEL))
        /* && !WellDefinednessCheck.isOn() */) {
            // TODO (DS): Deactivated this check for WellDefinednessCheck being
            // on inf the course of the refactoring
            return term; // FIXME: This case is only for SET Tests
        }
        else {
            return tf.createTerm(term.op(), term.subs(), term.boundVars(),
                    term.<P> modalContent(), labels);
        }
    }

    @Override
    public T label(T term, TermLabel label) {
        if (label == null) {
            return term;
        }
        else {
            return label(term, new ImmutableArray<TermLabel>(label));
        }
    }

    @Override
    public T shortcut(T term) {
        if ((term.op().equals(Junctor.AND)
        || term.op().equals(Junctor.OR))
        /* && WellDefinednessCheck.isOn() */) {
            // FIXME: Last condition is only for SET Tests
            // NOTE (DS): Removed the last condition in the course of the
            // refactoring.
            return addLabel(term,
                    ParameterlessTermLabel.SHORTCUT_EVALUATION_LABEL);
        }
        else {
            return term;
        }
    }

    @Override
    public T unlabel(T term) {
        return tf.createTerm(term.op(), term.subs(), term.boundVars(),
                term.<P> modalContent());
    }

    @Override
    public T unlabelRecursive(T term) {
        T[] subs = tf.createTermArray(term.arity());
        for (int i = 0; i < subs.length; i++) {
            subs[i] = unlabelRecursive(term.sub(i));
        }
        return tf.createTerm(term.op(), subs, term.boundVars(),
                term.<P> modalContent());
    }

    // -------------------------------------------------------------------------
    // reachability operators
    // -------------------------------------------------------------------------

    // -------------------------------------------------------------------------
    // sequence operators
    // -------------------------------------------------------------------------

    // -------------------------------------------------------------------------
    // misc (moved from key.util.MiscTools)
    // -------------------------------------------------------------------------

    /**
     * Removes leading updates from the passed term.
     */
    public static <T extends CCTerm<?, T>> T goBelowUpdates(T term) {
        while (term.op() instanceof UpdateApplication) {
            term = UpdateApplication.getTarget(term);
        }
        return term;
    }

    /**
     * Removes leading updates from the passed term.
     */
    public static <T extends CCTerm<?, T>> Pair<ImmutableList<T>, T> goBelowUpdates2(
            T term) {
        ImmutableList<T> updates = ImmutableSLList.<T> nil();
        while (term.op() instanceof UpdateApplication) {
            updates = updates.append(UpdateApplication.getUpdate(term));
            term = UpdateApplication.getTarget(term);
        }
        return new Pair<ImmutableList<T>, T>(updates, term);
    }

    @Override
    public ImmutableList<Sort> getSorts(Iterable<T> terms) {
        ImmutableList<Sort> result = ImmutableSLList.<Sort> nil();
        for (T t : terms) {
            result = result.append(t.sort());
        }
        return result;
    }

    @Override
    public T impPreserveLabels(T t1, T t2) {
        if ((t1.op() == Junctor.FALSE || t2.op() == Junctor.TRUE) &&
                (!t1.hasLabels() && !t2.hasLabels())) {
            return tt();
        }
        else if (t1.op() == Junctor.TRUE && !t1.hasLabels()) {
            return t2;
        }
        else if (t2.op() == Junctor.FALSE && !t2.hasLabels()) {
            return notPreserveLabels(t1);
        }
        else {
            return tf.createTerm(Junctor.IMP, t1, t2);
        }
    }

    @Override
    public T notPreserveLabels(T t) {
        if (t.op() == Junctor.TRUE && !t.hasLabels()) {
            return ff();
        }
        else if (t.op() == Junctor.FALSE && !t.hasLabels()) {
            return tt();
        }
        else if (t.op() == Junctor.NOT && !t.hasLabels()) {
            return t.sub(0);
        }
        else {
            return tf.createTerm(Junctor.NOT, t);
        }
    }

    @Override
    public T andPreserveLabels(Iterable<T> subTerms) {
        T result = tt();
        for (T sub : subTerms) {
            result = andPreserveLabels(result, sub);
        }
        return result;
    }

    @Override
    public T andPreserveLabels(T t1, T t2) {
        if ((t1.op() == Junctor.FALSE || t2.op() == Junctor.FALSE) &&
                (!t1.hasLabels() && !t2.hasLabels())) {
            return ff();
        }
        else if (t1.op() == Junctor.TRUE && !t1.hasLabels()) {
            return t2;
        }
        else if (t2.op() == Junctor.TRUE && !t2.hasLabels()) {
            return t1;
        }
        else {
            return tf.createTerm(Junctor.AND, t1, t2);
        }
    }

    @Override
    public T orPreserveLabels(Iterable<T> subTerms) {
        T result = ff();
        for (T sub : subTerms) {
            result = orPreserveLabels(result, sub);
        }
        return result;
    }

    @Override
    public T orPreserveLabels(T t1, T t2) {
        if ((t1.op() == Junctor.TRUE || t2.op() == Junctor.TRUE) &&
                (!t1.hasLabels() && !t2.hasLabels())) {
            return tt();
        }
        else if (t1.op() == Junctor.FALSE && !t1.hasLabels()) {
            return t2;
        }
        else if (t2.op() == Junctor.FALSE && !t2.hasLabels()) {
            return t1;
        }
        else {
            return tf.createTerm(Junctor.OR, t1, t2);
        }
    }
}