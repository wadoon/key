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

package de.uka.ilkd.key.java;

import org.key_project.common.core.logic.GenericTermBuilder;
import org.key_project.common.core.services.TermServices;

import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.JavaDLVisitor;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public interface JavaDLTermServices
        extends
        TermServices<SourceElement, NameAbstractionTable, JavaBlock, JavaDLVisitor, JavaDLTerm> {

    /**
     * Returns the {@link GenericTermBuilder} used to create {@link Term}s.
     * @return The {@link GenericTermBuilder} used to create {@link Term}s.
     */
    @SuppressWarnings("unchecked")
    @Override
    public abstract TermBuilder getTermBuilder();

    /**
     * Returns the {@link GenericTermBuilder} used to create {@link Term}s.
     * @return The {@link GenericTermBuilder} used to create {@link Term}s.
     */
    @SuppressWarnings("unchecked")
    @Override
    public abstract TermFactory getTermFactory();
 
    
    /**
     * returns the namespaces for functions, predicates etc.
     * @return the proof specific namespaces
     */
    @Override
    public abstract NamespaceSet getNamespaces();

}
