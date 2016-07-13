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

package org.key_project.bytecode.core.services;

import java.util.HashMap;

import org.key_project.bytecode.core.logic.Term;
import org.key_project.bytecode.core.logic.factories.TermBuilder;
import org.key_project.bytecode.core.logic.factories.TermFactory;
import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.NamespaceSet;
import org.key_project.common.core.logic.op.SortDependingFunction;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 */
public class TermServicesImpl implements BCTermServices {
    
    private NamespaceSet namespaces;
    
    private final TermBuilder tb;
    private final TermFactory tf;
    
    public TermServicesImpl() {
        tf = new TermFactory(new HashMap<Term, Term>());
        tb = new TermBuilder(tf, this);
        namespaces = new NamespaceSet();
    }
    
    public TermServicesImpl(NamespaceSet namespaces) {
        tf = new TermFactory(new HashMap<Term, Term>());
        tb = new TermBuilder(tf, this);
        this.namespaces = namespaces;
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
        return namespaces;
    }

    /**
     * @param namspaces the namspaces to set
     */
    public void setNamspaces(NamespaceSet namspaces) {
        this.namespaces = namspaces;
    }

    @Override
    public SortDependingFunction getFirstInstance(Name kind) {
        // TODO Auto-generated method stub
        return null;
    }

}
