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

package org.key_project.bytecode.core.logic;

import org.key_project.common.core.logic.CCTerm;
import org.key_project.common.core.logic.ModalContent;
import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.NamespaceSet;
import org.key_project.common.core.logic.factories.CCTermBuilder;
import org.key_project.common.core.logic.factories.CCTermFactory;
import org.key_project.common.core.logic.op.SortDependingFunction;
import org.key_project.common.core.services.TermServices;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 */
public class TermServicesImpl implements TermServices {

    @Override
    public <P extends ModalContent, T extends CCTerm<?, T>, TB extends CCTermBuilder<P, T>> TB getTermBuilder() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public <P extends ModalContent, T extends CCTerm<?, T>, TF extends CCTermFactory<P, T>> TF getTermFactory() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public NamespaceSet getNamespaces() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public SortDependingFunction getFirstInstance(Name kind) {
        // TODO Auto-generated method stub
        return null;
    }

}
