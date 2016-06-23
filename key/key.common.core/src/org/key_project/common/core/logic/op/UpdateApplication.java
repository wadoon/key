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

import org.key_project.common.core.logic.CCTerm;
import org.key_project.common.core.logic.Name;

/**
 * Singleton class defining a binary operator {u}t that applies updates u to
 * terms, formulas, or other updates t.
 */
public final class UpdateApplication extends AbstractOperator {

    public static final UpdateApplication UPDATE_APPLICATION =
            new UpdateApplication();

    private UpdateApplication() {
        super(new Name("update-application"), 2, false);
    }

    /**
     * @return the index of the subterm representing the update being applied
     */
    public static int updatePos() {
        return 0;
    }

    /**
     * @return the subterm representing the update being applies
     * @param t
     *            term with this operator as top level operator
     */
    @SuppressWarnings("unchecked")
    public static <T extends CCTerm<?, ?,?>> T getUpdate(T t) {
        assert t.op() == UPDATE_APPLICATION;
        return (T) t.sub(updatePos());
    }

    /**
     * @return the index of the subterm representing the formula/term/update
     *         that the update is applied to
     */
    public static int targetPos() {
        return 1;
    }

    /**
     * @return the subterm representing the formula/term the update is applied
     *         to
     * @param t
     *            term with this operator as top level operator
     */
    @SuppressWarnings("unchecked")
    public static <T extends CCTerm<?, ?,?>> T getTarget(T t) {
        assert t.op() == UPDATE_APPLICATION;
        return (T) t.sub(targetPos());
    }
}