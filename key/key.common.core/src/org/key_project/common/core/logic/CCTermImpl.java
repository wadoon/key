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

package org.key_project.common.core.logic;

import java.util.concurrent.atomic.AtomicInteger;

import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.common.core.logic.op.*;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.logic.visitors.CCTermVisitor;
import org.key_project.common.core.program.CCSourceElement;
import org.key_project.common.core.program.NameAbstractionTable;
import org.key_project.util.collection.*;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public abstract class CCTermImpl<P extends ModalContent, V extends CCTermVisitor<T>, T extends CCTerm<P, V, T>>
        implements CCTerm<P, V, T> {

    static enum ThreeValuedTruth {
        TRUE, FALSE, UNKNOWN
    }

    // ------------------------------------------------------------------
    // static fields
    // ------------------------------------------------------------------

    private static AtomicInteger serialNumberCounter = new AtomicInteger();

    static final ImmutableArray<QuantifiableVariable> EMPTY_VAR_LIST =
            new ImmutableArray<QuantifiableVariable>();

    static final ImmutableArray<TermLabel> EMPTY_LABEL_LIST =
            new ImmutableArray<TermLabel>();

    @SuppressWarnings("rawtypes")
    private static NameAbstractionTable FAILED = new NameAbstractionTable();

    @SuppressWarnings("unchecked")
    private static <S> NameAbstractionTable<S> failed() {
        return (NameAbstractionTable<S>) FAILED;
    }

    // -------------------------------------------------------------------
    // instance variables
    // -------------------------------------------------------------------

    protected final Operator op;
    protected final Sort sort;
    protected final ImmutableArray<T> subs;
    protected final ImmutableArray<QuantifiableVariable> boundVars;
    protected final P modalContent;
    private int depth = -1;
    private ThreeValuedTruth rigid = ThreeValuedTruth.UNKNOWN;
    private ImmutableSet<QuantifiableVariable> freeVars = null;
    private int hashcode = -1;
    final int serialNumber = serialNumberCounter.incrementAndGet();

    // caches

    /**
     * This flag indicates that the {@link Term} itself or one of its children
     * contains a non empty {@link JavaBlock}. {@link Term}s which provides a
     * {@link JavaBlock} directly or indirectly can't be cached because it is
     * possible that the contained meta information inside the {@link JavaBlock}
     * , e.g. PositionInfos, are different.
     */
    ThreeValuedTruth containsModalContentRecursive =
            ThreeValuedTruth.UNKNOWN;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    /**
     * 
     * TODO: Document.
     *
     * @param op
     * @param sort
     * @param subs
     * @param boundVars
     * @param javaBlock
     */
    public CCTermImpl(Operator op, Sort sort, ImmutableArray<T> subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            P javaBlock) {
        assert op != null;
        assert subs != null;
        this.op = op;
        this.sort = sort;
        this.subs = subs.size() == 0 ? emptyTermList() : subs;
        this.boundVars = boundVars == null ? EMPTY_VAR_LIST : boundVars;
        this.modalContent =
                javaBlock == null ? emptyModalContent() : javaBlock;
    }

    // -------------------------------------------------------------------------
    // abstract methods
    // -------------------------------------------------------------------------

    /**
     * TODO: Document.
     *
     * @return
     */
    protected abstract ImmutableArray<T> emptyTermList();

    /**
     * TODO: Document.
     *
     * @return
     */
    protected abstract P emptyModalContent();

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    @Override
    public Operator op() {
        return op;
    }

    @Override
    public <OpType> OpType op(Class<OpType> opClass)
            throws IllegalArgumentException {
        if (!opClass.isInstance(op)) {
            throw new IllegalArgumentException(
                    "Operator does not match the expected type:\n"
                            + "Operator type was: " + op.getClass() + "\n"
                            + "Expected type was: " + opClass);
        }
        return opClass.cast(op);
    }

    @Override
    public ImmutableArray<T> subs() {
        return subs;
    }

    @Override
    public T sub(int nr) {
        return subs.get(nr);
    }

    @Override
    public ImmutableArray<QuantifiableVariable> boundVars() {
        return boundVars;
    }

    @Override
    public ImmutableArray<QuantifiableVariable> varsBoundHere(int n) {
        return op.bindVarsAt(n) ? boundVars : EMPTY_VAR_LIST;
    }

    @Override
    public P modalContent() {
        return modalContent;
    }

    @Override
    public int arity() {
        return op.arity();
    }

    @Override
    public Sort sort() {
        return sort;
    }

    @Override
    public int depth() {
        if (depth == -1) {
            for (int i = 0, n = arity(); i < n; i++) {
                final int subTermDepth = sub(i).depth();
                if (subTermDepth > depth) {
                    depth = subTermDepth;
                }
            }
            depth++;
        }
        return depth;
    }

    @Override
    public boolean isRigid() {
        if (rigid == ThreeValuedTruth.UNKNOWN) {
            if (!op.isRigid()) {
                rigid = ThreeValuedTruth.FALSE;
            }
            else {
                rigid = ThreeValuedTruth.TRUE;
                for (int i = 0, n = arity(); i < n; i++) {
                    if (!sub(i).isRigid()) {
                        rigid = ThreeValuedTruth.FALSE;
                        break;
                    }
                }
            }
        }

        return rigid == ThreeValuedTruth.TRUE;
    }

    @Override
    public ImmutableSet<QuantifiableVariable> freeVars() {
        if (freeVars == null) {
            determineFreeVars();
        }
        return freeVars;
    }

    @Override
    public void execPostOrder(V visitor) {
        visitor.subtreeEntered(thisAsT());
        if (visitor.visitSubtree(thisAsT())) {
            for (int i = 0, ar = arity(); i < ar; i++) {
                sub(i).execPostOrder(visitor);
            }
        }
        visitor.visit(thisAsT());
        visitor.subtreeLeft(thisAsT());
    }

    @Override
    public void execPreOrder(V visitor) {
        visitor.subtreeEntered(thisAsT());
        visitor.visit(thisAsT());
        if (visitor.visitSubtree(thisAsT())) {
            for (int i = 0, ar = arity(); i < ar; i++) {
                sub(i).execPreOrder(visitor);
            }
        }
        visitor.subtreeLeft(thisAsT());
    }

    @SuppressWarnings("unchecked")
    @Override
    public boolean equalsModRenaming(Object o) {
        if (!(o instanceof CCTermImpl)) {
            return false;
        }

        if (o == this) {
            return true;
        }

        return unifyTermsModuloBoundRenaming(thisAsT(), (T) o,
                ImmutableSLList.<QuantifiableVariable> nil(),
                ImmutableSLList.<QuantifiableVariable> nil(), null);
    }

    /**
     * true iff <code>o</code> is syntactically equal to this term
     */
    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }

        if (o == null || o.getClass() != getClass()
                || hashCode() != o.hashCode()) {
            return false;
        }

        @SuppressWarnings("unchecked")
        final CCTermImpl<P, V, T> t = (CCTermImpl<P, V, T>) o;

        return op.equals(t.op) && t.hasLabels() == hasLabels()
                && subs.equals(t.subs) && boundVars.equals(t.boundVars)
                && modalContent.equals(t.modalContent);
    }

    @Override
    public final int hashCode() {
        if (hashcode == -1) {
            // compute into local variable first to be thread-safe.
            this.hashcode = computeHashCode();
        }
        return hashcode;
    }

    @Override
    public int serialNumber() {
        return serialNumber;
    }

    @Override
    public boolean hasLabels() {
        return false;
    }

    @Override
    public boolean containsLabel(TermLabel label) {
        return false;
    }

    @Override
    public TermLabel getLabel(Name termLabelName) {
        return null;
    }

    @Override
    public ImmutableArray<TermLabel> getLabels() {
        return EMPTY_LABEL_LIST;
    }

    @Override
    public boolean containsModalContentRecursive() {
        if (containsModalContentRecursive == ThreeValuedTruth.UNKNOWN) {
            ThreeValuedTruth result = ThreeValuedTruth.FALSE;
            if (modalContent != null && !modalContent.isEmpty()) {
                result = ThreeValuedTruth.TRUE;
            }
            else {
                for (int i = 0, arity = subs.size(); i < arity; i++) {
                    if (subs.get(i).containsModalContentRecursive()) {
                        result = ThreeValuedTruth.TRUE;
                        break;
                    }
                }
            }
            this.containsModalContentRecursive = result;
        }
        return containsModalContentRecursive == ThreeValuedTruth.TRUE;
    }

    /**
     * returns a linearized textual representation of this term
     */
    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer();
        if (!modalContent.isEmpty()) {
            if (op() == Modality.DIA) {
                sb.append("\\<").append(modalContent).append("\\> ");
            }
            else if (op() == Modality.BOX) {
                sb.append("\\[").append(modalContent).append("\\] ");
            }
            else {
                sb.append(op()).append("\\[").append(modalContent)
                        .append("\\] ");
            }
            sb.append("(").append(sub(0)).append(")");
            return sb.toString();
        }
        else {
            sb.append(op().name().toString());
            if (!boundVars.isEmpty()) {
                sb.append("{");
                for (int i = 0, n = boundVars.size(); i < n; i++) {
                    sb.append(boundVars.get(i));
                    if (i < n - 1) {
                        sb.append(", ");
                    }
                }
                sb.append("}");
            }
            if (arity() == 0) {
                return sb.toString();
            }
            sb.append("(");
            for (int i = 0, ar = arity(); i < ar; i++) {
                sb.append(sub(i));
                if (i < ar - 1) {
                    sb.append(",");
                }
            }
            sb.append(")");
        }

        return sb.toString();
    }

    // -------------------------------------------------------------------------
    // protected interface
    // -------------------------------------------------------------------------

    /**
     * performs the actual computation of the hash code and can be overwritten
     * by subclasses if necessary
     */
    protected int computeHashCode() {
        int hashcode = 5;
        hashcode = hashcode * 17 + op().hashCode();
        hashcode = hashcode * 17 + subs().hashCode();
        hashcode = hashcode * 17 + boundVars().hashCode();
        hashcode = hashcode * 17 + modalContent().hashCode();

        if (hashcode == -1) {
            hashcode = 0;
        }
        return hashcode;
    }

    /**
     * 
     * TODO: Document.
     *
     * @param t0
     * @param t1
     * @param ownBoundVars
     * @param cmpBoundVars
     * @return
     */
    protected boolean handleQuantifiableVariable(T t0, T t1,
            ImmutableList<QuantifiableVariable> ownBoundVars,
            ImmutableList<QuantifiableVariable> cmpBoundVars) {
        if (!((t1.op() instanceof QuantifiableVariable) && compareBoundVariables(
                (QuantifiableVariable) t0.op(), (QuantifiableVariable) t1.op(),
                ownBoundVars, cmpBoundVars))) {
            return false;
        }
        return true;
    }

    // Methods needed for equalsModRenaming

    /**
     * 
     * TODO: Document.
     *
     * @param t0
     * @param t1
     * @param ownBoundVars
     * @param cmpBoundVars
     * @param nat
     * @return
     */
    protected boolean descendRecursively(T t0, T t1,
            ImmutableList<QuantifiableVariable> ownBoundVars,
            ImmutableList<QuantifiableVariable> cmpBoundVars,
            NameAbstractionTable<CCSourceElement> nat) {

        for (int i = 0; i < t0.arity(); i++) {
            ImmutableList<QuantifiableVariable> subOwnBoundVars = ownBoundVars;
            ImmutableList<QuantifiableVariable> subCmpBoundVars = cmpBoundVars;

            if (t0.varsBoundHere(i).size() != t1.varsBoundHere(i).size()) {
                return false;
            }
            for (int j = 0; j < t0.varsBoundHere(i).size(); j++) {
                final QuantifiableVariable ownVar = t0.varsBoundHere(i).get(j);
                final QuantifiableVariable cmpVar = t1.varsBoundHere(i).get(j);
                if (ownVar.sort() != cmpVar.sort()) {
                    return false;
                }

                subOwnBoundVars = subOwnBoundVars.prepend(ownVar);
                subCmpBoundVars = subCmpBoundVars.prepend(cmpVar);
            }

            boolean newConstraint =
                    unifyTermsModuloBoundRenaming(t0.sub(i), t1.sub(i),
                            subOwnBoundVars,
                            subCmpBoundVars, nat);

            if (!newConstraint) {
                return false;
            }
        }

        return true;
    }

    // -------------------------------------------------------------------------
    // private instance methods
    // -------------------------------------------------------------------------

    @SuppressWarnings("unchecked")
    private T thisAsT() {
        // Since we assume that the the concrete class extending CCTermImpl is
        // from type T, the following cast is safe.
        return (T) this;
    }

    private void determineFreeVars() {
        freeVars = DefaultImmutableSet.<QuantifiableVariable> nil();

        if (op instanceof QuantifiableVariable) {
            freeVars = freeVars.add((QuantifiableVariable) op);
        }
        for (int i = 0, ar = arity(); i < ar; i++) {
            ImmutableSet<QuantifiableVariable> subFreeVars = sub(i).freeVars();
            for (int j = 0, sz = varsBoundHere(i).size(); j < sz; j++) {
                subFreeVars = subFreeVars.remove(varsBoundHere(i).get(j));
            }
            freeVars = freeVars.union(subFreeVars);
        }
    }

    /**
     * TODO: Document.
     *
     * @param t0
     * @param t1
     * @param ownBoundVars
     * @param cmpBoundVars
     * @param nat
     * @param failResult
     * @return
     */
    private boolean unifyTermsModuloBoundRenaming(T t0, T t1,
            ImmutableList<QuantifiableVariable> ownBoundVars,
            ImmutableList<QuantifiableVariable> cmpBoundVars,
            NameAbstractionTable<CCSourceElement> nat) {

        if (t0 == t1 && ownBoundVars.equals(cmpBoundVars)) {
            return true;
        }

        final Operator op0 = t0.op();

        if (op0 instanceof QuantifiableVariable) {
            return handleQuantifiableVariable(t0, t1, ownBoundVars,
                    cmpBoundVars);
        }

        final Operator op1 = t1.op();

        if (!(op0 instanceof CCProgramVariable) && op0 != op1) {
            return false;
        }

        if (t0.sort() != t1.sort() || t0.arity() != t1.arity()) {
            return false;
        }

        nat = unifyModalContent(t0, t1, nat);
        if (nat == FAILED) {
            return false;
        }

        return descendRecursively(t0, t1, ownBoundVars, cmpBoundVars, nat);
    }

    /**
     * Computes the name abstraction for t0 and t1. If the process fails,
     * failResult is returned. The method may not return null.
     *
     * TODO
     *
     * @param t0
     * @param t1
     * @param nat
     * @param failResult
     * @return
     */
    private NameAbstractionTable<CCSourceElement> unifyModalContent(T t0,
            T t1,
            NameAbstractionTable<CCSourceElement> nat) {

        if (!t0.modalContent().isEmpty() || !t1.modalContent().isEmpty()) {
            nat = checkNat(nat);
            if (!t0.modalContent().equalsModRenaming(t1.modalContent(), nat)) {
                return failed();
            }
        }

        if (!(t0.op() instanceof SchemaVariable)
                && t0.op() instanceof CCProgramVariable) {
            if (!(t1.op() instanceof CCProgramVariable)) {
                return failed();
            }
            nat = checkNat(nat);

            CCProgramVariable op0 = (CCProgramVariable) t0.op();
            CCProgramVariable op1 = (CCProgramVariable) t1.op();

            if (!op0.equalsModRenaming(
                    op1, nat)) {
                return failed();
            }
        }

        return nat;
    }

    // -------------------------------------------------------------------------
    // private static methods
    // -------------------------------------------------------------------------

    // Methods needed for equalsModRenaming

    /**
     * compare two quantifiable variables if they are equal modulo renaming
     * 
     * @param ownVar
     *            first QuantifiableVariable to be compared
     * @param cmpVar
     *            second QuantifiableVariable to be compared
     * @param ownBoundVars
     *            variables bound above the current position
     * @param cmpBoundVars
     *            variables bound above the current position
     */
    private static boolean compareBoundVariables(QuantifiableVariable ownVar,
            QuantifiableVariable cmpVar,
            ImmutableList<QuantifiableVariable> ownBoundVars,
            ImmutableList<QuantifiableVariable> cmpBoundVars) {

        final int ownNum = indexOf(ownVar, ownBoundVars);
        final int cmpNum = indexOf(cmpVar, cmpBoundVars);

        if (ownNum == -1 && cmpNum == -1) {
            // if both variables are not bound the variables have to be the
            // same object
            return ownVar == cmpVar;
        }

        // otherwise the variables have to be bound at the same point (and both
        // be bound)
        return ownNum == cmpNum;
    }

    /**
     * @return the index of the first occurrence of <code>var</code> in
     *         <code>list</code>, or <code>-1</code> if the variable is not an
     *         element of the list
     */
    private static int indexOf(QuantifiableVariable var,
            ImmutableList<QuantifiableVariable> list) {
        int res = 0;
        while (!list.isEmpty()) {
            if (list.head() == var) {
                return res;
            }
            ++res;
            list = list.tail();
        }
        return -1;
    }

    private static <S> NameAbstractionTable<S> checkNat(
            NameAbstractionTable<S> nat) {
        if (nat == null) {
            return new NameAbstractionTable<S>();
        }
        return nat;
    }

}