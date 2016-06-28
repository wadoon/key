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

package org.key_project.common.core.services;

import org.key_project.common.core.logic.CCTerm;
import org.key_project.common.core.logic.ModalContent;
import org.key_project.common.core.logic.NamespaceSet;
import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.factories.CCTermBuilder;
import org.key_project.common.core.logic.factories.CCTermFactory;
import org.key_project.common.core.logic.op.SortDependingFunction;

/**
 * This interface defines the basic functionalities of services
 * required to construct {@link Term}s.
 *
 * @author Richard Bubel
 *
 * @param <P>
 * @param <T>
 */
public interface TermServices<P extends ModalContent<?>, T extends CCTerm<?, P, ?, T>, TB extends CCTermBuilder<P, T>, TF extends CCTermFactory<P, T>> {

    /**
     * Returns the {@link CCTermBuilder} used to create {@link Term}s.
     * @return The {@link CCTermBuilder} used to create {@link Term}s.
     */
    public abstract TB getTermBuilder();

    /**
     * Returns the {@link CCTermBuilder} used to create {@link Term}s.
     * @return The {@link CCTermBuilder} used to create {@link Term}s.
     */
    public abstract TF getTermFactory();

    /**
     * returns the namespaces for functions, predicates etc.
     * @return the proof specific namespaces
     */
    public abstract NamespaceSet getNamespaces();

    /**
     * Returns the first instance of the function symbol of the given kind. 
     *
     * @param kind Kind of the function.
     * @return The first instance of the function symbol of the given kind.
     */
    public abstract SortDependingFunction getFirstInstance(Name kind);
}