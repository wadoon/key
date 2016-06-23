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

import org.key_project.common.core.logic.CCTermImpl;
import org.key_project.common.core.logic.op.Modality;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

/**
 * The currently only class implementing the Term interface. TermFactory should
 * be the only class dealing directly with the TermImpl class.
 */
class TermImpl extends CCTermImpl<JavaBlock, Visitor, Term>
        implements Term {

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

}
