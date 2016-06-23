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

import java.util.HashMap;

import org.key_project.bytecode.core.logic.factories.TermBuilder;
import org.key_project.bytecode.core.logic.factories.TermFactory;
import org.key_project.bytecode.core.logic.services.BCTermServices;
import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.NamespaceSet;
import org.key_project.common.core.logic.op.SortDependingFunction;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 */
public class TermServicesImpl implements BCTermServices {

    private static final BCTermServices INSTANCE = new TermServicesImpl();
    
    public static BCTermServices instance() {
        return INSTANCE;
    }
    
    private final TermBuilder tb;
    private final TermFactory tf;
    
    private TermServicesImpl() {
        tf = new TermFactory(new HashMap<Term, Term>());
        tb = new TermBuilder(tf, this);
    }
    
    @Override
    public TermBuilder getTermBuilder() {
        return tb;
    }

    @Override
    public TermFactory getTermFactory() {
        return tf;
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
