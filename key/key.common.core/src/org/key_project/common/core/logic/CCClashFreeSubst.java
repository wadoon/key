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

package org.key_project.common.core.logic;

import java.lang.reflect.Array;

import org.key_project.common.core.logic.factories.CCTermBuilder;
import org.key_project.common.core.logic.factories.CCTermFactory;
import org.key_project.common.core.logic.op.LogicVariable;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.visitors.CCDefaultVisitor;
import org.key_project.common.core.logic.visitors.CCTermVisitor;
import org.key_project.common.core.services.TermServices;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

public class CCClashFreeSubst<P extends ModalContent<?>, V extends CCTermVisitor<T>, T extends CCTerm<?, P, V, T>> {
    protected QuantifiableVariable v;
    protected T s;
    protected ImmutableSet<QuantifiableVariable> svars;
    protected final TermServices<P, T, ?, ?> services;
    
    private final Class<T> clazz;

    public <TB extends CCTermBuilder<P, T>, TF extends CCTermFactory<P, T>> CCClashFreeSubst(QuantifiableVariable v, T s,
                            TermServices<P, T, TB, TF> services, Class<T> clazz) {
        this.services = services;
        this.v = v;
        this.s = s;
        svars = s.freeVars();
        this.clazz = clazz;
    }

    protected QuantifiableVariable getVariable() {
        return v;
    }

    protected T getSubstitutedTerm() {
        return s;
    }

    /**
     * substitute <code>s</code> for <code>v</code> in <code>t</code>, avoiding
     * collisions by replacing bound variables in <code>t</code> if necessary.
     */
    public T apply(T t) {
        if (!t.freeVars().contains(v)) {
            return t;
        }
        else
            return apply1(t);
    }

    /**
     * substitute <code>s</code> for <code>v</code> in <code>t</code>, avoiding
     * collisions by replacing bound variables in <code>t</code> if necessary.
     * It is assumed, that <code>t</code> contains a free occurrence of
     * <code>v</code>.
     */
    protected T apply1(T t) {
        if (t.op() == v) {
            return s;
        }
        else {
            return applyOnSubterms(t);
        }
    }

    // XXX
    protected static ImmutableArray<QuantifiableVariable> getSingleArray(
            ImmutableArray<QuantifiableVariable>[] bv) {
        if (bv == null) {
            return null;
        }
        ImmutableArray<QuantifiableVariable> result = null;
        for (ImmutableArray<QuantifiableVariable> arr : bv) {
            if (arr != null && !arr.isEmpty()) {
                if (result == null) {
                    result = arr;
                }
                else {
                    assert arr.equals(result) : "expected: " + result
                            + "\nfound: " + arr;
                }
            }
        }
        return result;
    }

    /**
     * substitute <code>s</code> for <code>v</code> in every subterm of
     * <code>t</code>, and build a new term. It is assumed, that one of the
     * subterms contains a free occurrence of <code>v</code>, and that the case
     * <code>v==t<code> is already
     * handled.
     */
    private T applyOnSubterms(T t) {
        final int arity = t.arity();
        @SuppressWarnings("unchecked")
        final T[] newSubterms = (T[]) Array.newInstance(clazz, arity);
        @SuppressWarnings("unchecked")
        final ImmutableArray<QuantifiableVariable>[] newBoundVars =
                new ImmutableArray[arity];
        for (int i = 0; i < arity; i++) {
            applyOnSubterm(t, i, newSubterms, newBoundVars);
        }
        return services
                .getTermBuilder()
                .tf()
                .createTerm(t.op(), newSubterms, getSingleArray(newBoundVars),
                        t.modalContent(), t.getLabels());
    }

    /**
     * Apply the substitution of the subterm <code>subtermIndex</code> of
     * term/formula <code>completeTerm</code>. The result is stored in
     * <code>newSubterms</code> and <code>newBoundVars</code> (at index
     * <code>subtermIndex</code>)
     */
    protected void applyOnSubterm(T completeTerm,
            int subtermIndex,
            T[] newSubterms,
            ImmutableArray<QuantifiableVariable>[] newBoundVars) {
        if (subTermChanges(completeTerm.varsBoundHere(subtermIndex),
                completeTerm.sub(subtermIndex))) {
            final QuantifiableVariable[] nbv =
                    new QuantifiableVariable[completeTerm.varsBoundHere(
                            subtermIndex).size()];
            applyOnSubterm(0,
                    completeTerm.varsBoundHere(subtermIndex),
                    nbv,
                    subtermIndex,
                    completeTerm.sub(subtermIndex),
                    newSubterms);
            newBoundVars[subtermIndex] =
                    new ImmutableArray<QuantifiableVariable>(nbv);
        }
        else {
            newBoundVars[subtermIndex] =
                    completeTerm.varsBoundHere(subtermIndex);
            newSubterms[subtermIndex] = completeTerm.sub(subtermIndex);
        }
    }

    /**
     * Perform the substitution on <code>subTerm</code> bound by the variables
     * in <code>boundVars</code>, starting with the variable at index
     * <code>varInd</code>. Put the resulting bound variables (which might be
     * new) into <code>newBoundVars</code>, starting from position
     * <code>varInd</code>, and the resulting subTerm into
     * <code>newSubterms[subInd]</code>.
     * <P>
     * It is assumed that <code>v</code> occurrs free in in this quantified
     * subterm, i.e. it occurrs free in <code>subTerm</code>, but does not
     * occurr in <code>boundVars</code> from <code>varInd</code> upwards..
     */
    private void applyOnSubterm(int varInd,
            ImmutableArray<QuantifiableVariable> boundVars,
            QuantifiableVariable[] newBoundVars,
            int subInd,
            T subTerm,
            T[] newSubterms
            ) {
        if (varInd >= boundVars.size()) {
            newSubterms[subInd] = apply1(subTerm);
        }
        else {
            QuantifiableVariable qv = boundVars.get(varInd);
            if (svars.contains(qv)) {
                /* Here is the clash case all this is about! Hurrah! */

                // Determine Variable names to avoid
                VariableCollectVisitor<V, T> vcv = new VariableCollectVisitor<V, T>();
                @SuppressWarnings("unchecked")
                V vcvV = (V) vcv;
                ImmutableSet<QuantifiableVariable> usedVars;
                subTerm.execPostOrder(vcvV);
                usedVars = svars;
                usedVars = usedVars.union(vcv.vars());
                for (int i = varInd + 1; i < boundVars.size(); i++) {
                    usedVars =
                            usedVars.add(boundVars.get(i));
                }
                // Get a new variable with a fitting name.
                QuantifiableVariable qv1 = newVarFor(qv, usedVars);

                // Substitute that for the old one.
                newBoundVars[varInd] = qv1;
                new CCClashFreeSubst<P, V, T>(qv, services.getTermBuilder().var(qv1),
                        services, clazz)
                        .applyOnSubterm1(varInd + 1, boundVars, newBoundVars,
                                subInd, subTerm, newSubterms);
                // then continue recursively, on the result.
                applyOnSubterm(varInd + 1,
                        new ImmutableArray<QuantifiableVariable>(newBoundVars),
                        newBoundVars,
                        subInd, newSubterms[subInd], newSubterms);
            }
            else {
                newBoundVars[varInd] = qv;
                applyOnSubterm(varInd + 1, boundVars, newBoundVars,
                        subInd, subTerm, newSubterms);
            }
        }
    }

    /**
     * Same as applyOnSubterm, but v doesn't have to occurr free in the
     * considered quantified subterm. It is however assumed that no more clash
     * can occurr.
     */
    private void applyOnSubterm1(int varInd,
            ImmutableArray<QuantifiableVariable> boundVars,
            QuantifiableVariable[] newBoundVars,
            int subInd,
            T subTerm,
            T[] newSubterms
            ) {
        if (varInd >= boundVars.size()) {
            newSubterms[subInd] = apply(subTerm);
        }
        else {
            QuantifiableVariable qv = boundVars.get(varInd);
            newBoundVars[varInd] = qv;
            if (qv == v) {
                newSubterms[subInd] = subTerm;
                for (int i = varInd; i < boundVars.size(); i++) {
                    newBoundVars[i] = boundVars.get(varInd);
                }
            }
            else {
                applyOnSubterm1(varInd + 1, boundVars, newBoundVars,
                        subInd, subTerm, newSubterms);
            }
        }
    }

    /**
     * returns true if <code>subTerm</code> bound by <code>boundVars</code>
     * would change under application of this substitution. This is the case, if
     * <code>v</code> occurrs free in <code>subTerm</code>, but does not occurr
     * in <code>boundVars</code>.
     * 
     * @returns true if <code>subTerm</code> bound by <code>boundVars</code>
     *          would change under application of this substitution
     */
    protected boolean subTermChanges(
            ImmutableArray<QuantifiableVariable> boundVars,
            T subTerm) {
        if (!subTerm.freeVars().contains(v)) {
            return false;
        }
        else {
            for (int i = 0; i < boundVars.size(); i++) {
                if (v == boundVars.get(i)) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * returns a new variable that has a name derived from that of
     * <code>var</code>, that is different from any of the names of variables in
     * <code>usedVars</code>.
     * <P>
     * Assumes that <code>var</code> is a @link{LogicVariable}.
     */
    protected QuantifiableVariable newVarFor(QuantifiableVariable var,
            ImmutableSet<QuantifiableVariable> usedVars) {
        LogicVariable lv = (LogicVariable) var;
        String stem = var.name().toString();
        int i = 1;
        while (!nameNewInSet((stem + i), usedVars)) {
            i++;
        }
        return new LogicVariable(new Name(stem + i), lv.sort());
    }

    /**
     * returns true if there is no object named <code>n</code> in the set
     * <code>s</code>
     */
    private boolean nameNewInSet(String n,
            ImmutableSet<QuantifiableVariable> qvars) {
        for (QuantifiableVariable qvar : qvars) {
            if (qvar.name().toString().equals(n)) {
                return false;
            }
        }
        return true;
    }

    // This helper is used in other places as well. Perhaps make it toplevel one
    // day.
    /**
     * A Visitor class to collect all (not just the free) variables occurring in
     * a term.
     */
    public static class VariableCollectVisitor <V extends CCTermVisitor<T>, T extends CCTerm<?, ?, V, T>> extends CCDefaultVisitor<T> {
        /** the collected variables */
        private ImmutableSet<QuantifiableVariable> vars;

        /** creates the Variable collector */
        public VariableCollectVisitor() {
            vars = DefaultImmutableSet.<QuantifiableVariable> nil();
        }

        public void visit(T t) {
            if (t.op() instanceof QuantifiableVariable) {
                vars = vars.add((QuantifiableVariable) t.op());
            }
            else {
                for (int i = 0; i < t.arity(); i++) {
                    ImmutableArray<QuantifiableVariable> vbh =
                            t.varsBoundHere(i);
                    for (int j = 0; j < vbh.size(); j++) {
                        vars = vars.add(vbh.get(j));
                    }
                }
            }
        }

        /** the set of all occurring variables. */
        public ImmutableSet<QuantifiableVariable> vars() {
            return vars;
        }
    }

}