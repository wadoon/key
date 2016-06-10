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

import org.key_project.common.core.logic.GenericNamespaceSet;
import org.key_project.common.core.logic.GenericTerm;
import org.key_project.common.core.logic.GenericTermBuilder;
import org.key_project.common.core.logic.GenericTermFactory;
import org.key_project.common.core.logic.ModalContent;
import org.key_project.common.core.logic.Visitor;
import org.key_project.common.core.program.GenericNameAbstractionTable;

/**
 * This interface defines the basic functionalities of services
 * required to construct {@link Term}s.
 *
 * @author Richard Bubel
 *
 * @param <S> SourceElement type
 * @param <T> Term type
 * @param <V> Visitor type
 * @param <N> Name abstraction table type
 * @param <P> Program type
 */
public interface TermServices<S, T extends GenericTerm<S, T, V, N>, V extends Visitor<S, V, T, N>, N extends GenericNameAbstractionTable<S>, P extends ModalContent<S, N>> {

    /**
     * returns the namespaces for functions, predicates etc.
     * @return the proof specific namespaces
     */
    public abstract GenericNamespaceSet getNamespaces();

    /**
     * Returns the {@link GenericTermBuilder} used to create {@link Term}s.
     * @return The {@link GenericTermBuilder} used to create {@link Term}s.
     */
    public abstract GenericTermBuilder getTermBuilder();

    /**
     * Returns the {@link GenericTermBuilder} used to create {@link Term}s.
     * @return The {@link GenericTermBuilder} used to create {@link Term}s.
     */
    public abstract GenericTermFactory<S,T,V,N,P> getTermFactory();

}