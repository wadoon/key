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

package org.key_project.common.core.logic.op;

import java.lang.reflect.Array;

import org.key_project.common.core.logic.CCClashFreeSubst;
import org.key_project.common.core.logic.CCTerm;
import org.key_project.common.core.logic.ModalContent;
import org.key_project.common.core.logic.factories.CCTermBuilder;
import org.key_project.common.core.logic.visitors.CCTermVisitor;
import org.key_project.common.core.services.TermServices;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

public class WaryClashFreeSubst<V extends CCTermVisitor<T>, T extends CCTerm<V, T>>
        extends CCClashFreeSubst<V, T> {

    /** depth of recursion of the <code>apply</code> method */
    private int depth = 0;

    /** the formula should be prepended with a quantifier */
    protected boolean createQuantifier = false;

    /**
     * variable with which the original variable should be substituted below
     * modalities
     */
    protected QuantifiableVariable newVar = null;
    protected T newVarTerm = null;

    private final Class<T> clazz;

    /**
     * variables occurring within the original term and within the term to be
     * substituted
     */
    protected ImmutableSet<QuantifiableVariable> warysvars = null;

    public WaryClashFreeSubst(QuantifiableVariable v, T s,
            TermServices services, Class<T> clazz) {
        super(v, s, services, clazz);
        this.clazz = clazz;
        warysvars = null;
    }

    /**
     * substitute <code>s</code> for <code>v</code> in <code>t</code>, avoiding
     * collisions by replacing bound variables in <code>t</code> if necessary.
     */
    public T apply(T t) {
        T res;

        if (depth == 0) {
            if (!getSubstitutedTerm().isRigid())
                findUsedVariables(t);
        }

        ++depth;
        try {
            res = super.apply(t);
        }
        finally {
            --depth;
        }

        if (createQuantifier && depth == 0)
            res = addWarySubst(res);

        return res;
    }

    /**
     * Determine a set of variables that do already appear within <code>t</code>
     * or the substituted term, and whose names should not be used for free
     * variables
     */
    private void findUsedVariables(T t) {
        VariableCollectVisitor<V, T> vcv;

        vcv = new VariableCollectVisitor<V, T>();
        @SuppressWarnings("unchecked")
        V vcvV = (V) vcv;

        getSubstitutedTerm().execPostOrder(vcvV);
        warysvars = vcv.vars();

        vcv = new VariableCollectVisitor<V, T>();
        t.execPostOrder(vcvV);
        warysvars = warysvars.union(vcv.vars());
    }

    /**
     * substitute <code>s</code> for <code>v</code> in <code>t</code>, avoiding
     * collisions by replacing bound variables in <code>t</code> if necessary.
     * It is assumed, that <code>t</code> contains a free occurrence of
     * <code>v</code>.
     */
    protected T apply1(T t) {
        // don't move to a different modality level
        if (!getSubstitutedTerm().isRigid()) {
            if (t.op() instanceof Modality)
                return applyOnModality(t);
            if (t.op() instanceof UpdateApplication)
                return applyOnUpdate(t);
        }
        if (t.op() instanceof Transformer)
            return applyOnTransformer(t);
        return super.apply1(t);
    }

    /**
     * Apply the substitution (that replaces a variable with a non-rigid term)
     * on t, which has a modality as top-level operator. This is done by
     * creating a (top-level) existential quantifier. This method is only called
     * from <code>apply1</code> for substitutions with non-rigid terms
     *
     * PRECONDITION: <code>warysvars != null</code>
     */
    private T applyOnModality(T t) {
        return applyBelowModality(t);
    }

    /**
     * Apply the substitution (that replaces a variable with a term) on t, which
     * has a transformer procedure as top-level operator. This is done by
     * creating a (top-level) existential quantifier. This method is only called
     * from <code>apply1</code> for substitutions with non-rigid terms
     *
     * PRECONDITION: <code>warysvars != null</code>
     */
    private T applyOnTransformer(T t) {
        return applyBelowTransformer(t);
    }

    /**
     * Apply the substitution (that replaces a variable with a non-rigid term)
     * on t, which has an update operator as top-level operator. This is done by
     * creating a (top-level) existential quantifier. This method is only called
     * from <code>apply1</code> for substitutions with non-rigid terms
     *
     * PRECONDITION: <code>warysvars != null</code>
     */
    private T applyOnUpdate(T t) {

        // only the last child is below the update
        final T target = UpdateApplication.getTarget(t);
        if (!target.freeVars().contains(getVariable()))
            return super.apply1(t);

        @SuppressWarnings("unchecked")
        final T[] newSubterms = (T[]) Array.newInstance(clazz, t.arity());
        @SuppressWarnings("unchecked")
        final ImmutableArray<QuantifiableVariable>[] newBoundVars =
                new ImmutableArray[t.arity()];

        for (int i = 0; i < t.arity(); i++) {
            if (i != UpdateApplication.targetPos())
                applyOnSubterm(t, i, newSubterms, newBoundVars);
        }

        newBoundVars[UpdateApplication.targetPos()] =
                t.varsBoundHere(UpdateApplication.targetPos());
        final boolean addSubst =
                subTermChanges(t.varsBoundHere(UpdateApplication.targetPos()),
                        target);
        newSubterms[UpdateApplication.targetPos()] =
                addSubst ? substWithNewVar(target)
                        : target;

        T result =
                services.<ModalContent, T, CCTermBuilder<ModalContent, T>> getTermBuilder()
                        .tf()
                        .createTerm(t.op(),
                                newSubterms,
                                getSingleArray(newBoundVars),
                                t.modalContent());

        return result;
    }

    /**
     * Apply the substitution to a term/formula below a modality or update
     */
    private T applyBelowModality(T t) {
        return substWithNewVar(t);
    }

    /**
     * Apply the substitution to a term/formula below a transformer procedure
     */
    private T applyBelowTransformer(T t) {
        return substWithNewVar(t);
    }

    /**
     * Rename the original variable to be substituted to <code>newVar</code>
     */
    private T substWithNewVar(T t) {
        createVariable();
        final CCClashFreeSubst<V, T> cfs =
                new CCClashFreeSubst<V, T>(getVariable(),
                        newVarTerm, services, clazz);
        return cfs.apply(t);
    }

    /**
     * Create a new logic variable to be used for substitutions below modalities
     */
    void createVariable() {
        if (!createQuantifier) {
            createQuantifier = true;

            if (getSubstitutedTerm().freeVars().contains(getVariable())) {
                // in this case one might otherwise get collisions, as the
                // substitution might be carried out partially within the scope
                // of the original substitution operator
                newVar = newVarFor(getVariable(), warysvars);
            }
            else {
                newVar = getVariable();
            }
            
            newVarTerm =
                    services
                            .<ModalContent, T, CCTermBuilder<ModalContent, T>> getTermBuilder()
                            .var(newVar);
        }
    }

    /**
     * Prepend the given term with a wary substitution (substituting
     * <code>newVar</code> with <code>getSubstitutedTerm()</code>)
     */
    T addWarySubst(T t) {
        createVariable();
        return services.<ModalContent, T, CCTermBuilder<ModalContent, T>> getTermBuilder()
                .subst(
                        // WarySubstOp.SUBST, // WarySubstOp is the standard
                        newVar,
                        getSubstitutedTerm(),
                        t);
    }
}