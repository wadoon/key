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

import org.key_project.common.core.logic.CCTerm;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.SortedOperator;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

/**
 * {@link RuntimeException} thrown when creating a term failed.
 */
public class TermCreationException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    public TermCreationException(String errorMessage) {
        super(errorMessage);
    }

    public <T extends CCTerm<?, T>> TermCreationException(Operator op, T failed, Sort s) {
        super(getErrorMessage(op, failed, s));
    }

    protected static <T extends CCTerm<?, T>> String getErrorMessage(
            Operator op, T failed, Sort s) {
        ImmutableArray<T> subs = failed.subs();
        for (int i = 0, n = subs.size(); i < n; i++) {
            T sub = subs.get(i);
            assert sub == failed.subs().get(i);
        }

        return "Building a term failed. Normally there is an arity mismatch "
                + "or one of the subterms' sorts "
                + "is not compatible (e.g. like the \'2\' in \"true & 2\")\n"
                + "The top level operator was "
                + op
                + "(Sort: "
                + s
                + ")"
                + (op instanceof SortedOperator ? "; its expected arg sorts were:\n"
                        + argsToString((SortedOperator) op)
                        : "") + "\nThe subterms were:\n" + subsToString(subs);
    }

    private static String argsToString(SortedOperator f) {
        StringBuffer sb = new StringBuffer();
        for (int i = 0; i < f.arity(); i++) {
            sb.append((i + 1) + ".) ");
            sb.append("sort: "
                    + f.argSort(i)
                    + (f.argSort(i) == null ? "" : ", sort hash: "
                            + f.argSort(i).hashCode()) + "\n");
        }
        return sb.toString();
    }

    private static <T extends CCTerm<?, T>> String subsToString(
            ImmutableArray<T> subs) {
        StringBuffer sb = new StringBuffer();
        for (int i = 0, n = subs.size(); i < n; i++) {
            sb.append((i + 1) + ".) ");
            T subi = subs.get(i);
            if (subi != null) {
                sb.append(subi);
                Sort subiSort = subi.sort();
                if (subiSort != null) {
                    sb.append("(sort: " + subi.sort() + ", sort hash: "
                            + subi.sort().hashCode() + ")\n");
                }
                else {
                    sb.append("(Unknown sort, \"null pointer\")");
                }
            }
            else {
                sb.append(" !null!\n");
            }

        }
        return sb.toString();
    }
}
