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

package org.key_project.common.core.logic;

import org.key_project.util.collection.ImmutableSet;

/**
 * This interface defines the basic functionalities of services
 * required to construct {@link Term}s.
 * @author Richard Bubel
 */
public interface TermServices<T extends DLTerm<? extends DLVisitor<T>>, P extends Program>  {

    /**
     * returns the namespaces for functions, predicates etc.
     * @return the proof specific namespaces
     */
    public abstract NamespaceSet getNamespaces();

    /**
     * Returns the {@link TermBuilder} used to create {@link Term}s.
     * @return The {@link TermBuilder} used to create {@link Term}s.
     */
    public abstract DLTermBuilder<T> getTermBuilder();

    /**
     * Returns the {@link TermBuilder} used to create {@link Term}s.
     * @return The {@link TermBuilder} used to create {@link Term}s.
     */
    public abstract DLTermFactory<T,P> getTermFactory();
    
    
    /**
     * 
     */
    public abstract ImmutableSet<Sort> getDirectSuperSorts(Sort s);

    public abstract Sort getAnySort();

    public abstract Sort getFormulaSort();

    public abstract Sort getUpdateSort();

    public abstract Sort getTermLabelSort();

}