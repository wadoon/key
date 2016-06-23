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

package org.key_project.common.core.logic.op;

import org.key_project.common.core.logic.CCTerm;
import org.key_project.common.core.logic.ModalContent;
import org.key_project.common.core.logic.Name;
import org.key_project.common.core.services.TermServices;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public abstract class CCSubstOp<P extends ModalContent, T extends CCTerm<P, ?, T>> extends AbstractOperator {

    /**
     * Constructs a new {@link CCSubstOp} for the given name.
     *
     * @param name The name for the operation.
     */
    protected CCSubstOp(Name name) {
        super(name, 2, new Boolean[] { false, true }, true);
    }

    /**
     * Apply this substitution operator to <code>term</code>, which has this
     * operator as top-level operator
     * 
     * @param services
     *            TODO
     */
    public abstract T apply(T term, TermServices<P, T, ?, ?> services);

}