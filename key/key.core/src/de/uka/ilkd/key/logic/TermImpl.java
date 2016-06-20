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

package de.uka.ilkd.key.logic;

import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.op.SchemaVariable;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * The currently only class implementing the Term interface. TermFactory should
 * be the only class dealing directly with the TermImpl class.
 */
class TermImpl extends CCTermImpl<JavaBlock, Visitor, Term> implements Term {

    private static final ImmutableArray<Term> EMPTY_TERM_LIST =
            new ImmutableArray<Term>();

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public TermImpl(Operator op, Sort sort, ImmutableArray<Term> subs,
            ImmutableArray<QuantifiableVariable> boundVars, JavaBlock javaBlock) {
        super(op, sort, subs, boundVars, javaBlock);
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
    // implementation of inherited abstract methods
    // -------------------------------------------------------------------------

    @Override
    protected ImmutableArray<Term> emptyTermList() {
        return EMPTY_TERM_LIST;
    }

    @Override
    protected JavaBlock emptyModalContent() {
        return JavaBlock.EMPTY_JAVABLOCK;
    }

    @Override
    protected NameAbstractionTable unifyModalContent(Term t0, Term t1,
            NameAbstractionTable nat, NameAbstractionTable failResult) {

        if (!t0.modalContent().isEmpty() || !t1.modalContent().isEmpty()) {
            nat = checkNat(nat);
            if (!t0.modalContent().equalsModRenaming(t1.modalContent(), nat)) {
                return failResult;
            }
        }

        if (!(t0.op() instanceof SchemaVariable)
                && t0.op() instanceof ProgramVariable) {
            if (!(t1.op() instanceof ProgramVariable)) {
                return failResult;
            }
            nat = checkNat(nat);
            if (!((ProgramVariable) t0.op()).equalsModRenaming(
                    (ProgramVariable) t1.op(), nat)) {
                return failResult;
            }
        }

        return nat;
    }
    
    @Override
    protected boolean unifyTermsModuloBoundRenaming(Term t0, Term t1,
            ImmutableList<QuantifiableVariable> ownBoundVars,
            ImmutableList<QuantifiableVariable> cmpBoundVars,
            NameAbstractionTable nat,
            NameAbstractionTable failResult){

            if (t0 == t1 && ownBoundVars.equals(cmpBoundVars)) {
                return true;
            }

            final Operator op0 = t0.op();

            if (op0 instanceof QuantifiableVariable) {
                return handleQuantifiableVariable(t0, t1, ownBoundVars,
                        cmpBoundVars);
            }

            final Operator op1 = t1.op();

            if (!(op0 instanceof ProgramVariable) && op0 != op1) {
                return false;
            }

            if (t0.sort() != t1.sort() || t0.arity() != t1.arity()) {
                return false;
            }

            nat = unifyModalContent(t0, t1, nat, failResult);
            if (nat == failResult) {
                return false;
            }

            return descendRecursively(t0, t1, ownBoundVars, cmpBoundVars, nat);
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private static NameAbstractionTable checkNat(NameAbstractionTable nat) {
        if (nat == null) {
            return new NameAbstractionTable();
        }
        return nat;
    }

}
