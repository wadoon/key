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
import org.key_project.common.core.logic.visitors.CCTermVisitor;
import org.key_project.common.core.services.TermServices;

/**
 * A WarySubstOp operator. Instances of this class are supposed to be
 * Singletons.
 *
 * @author Dominic Scheurer
 */
public abstract class CCWarySubstOp<P extends ModalContent<?>, V extends CCTermVisitor<T>, T extends CCTerm<?, P, V, T>>
        extends CCSubstOp<P, T> {

    /**
     * TODO: Document.
     *
     * @param name
     */
    protected CCWarySubstOp(Name name) {
        super(name);
    }

    public T apply(T term, TermServices<P, T, ?, ?> services, Class<T> clazz) {
        QuantifiableVariable v = term.varsBoundHere(1).get(0);
        WaryClashFreeSubst<P, V, T> cfSubst =
                new WaryClashFreeSubst<P, V, T>(v, term.sub(0), services, clazz);
        return cfSubst.apply(term.sub(1));
    }

}