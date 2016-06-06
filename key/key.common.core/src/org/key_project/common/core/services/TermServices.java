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
import org.key_project.common.core.logic.GenericTermBuilder;
import org.key_project.common.core.logic.GenericTermFactory;

import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;

/**
 * This interface defines the basic functionalities of services
 * required to construct {@link Term}s.
 * @author Richard Bubel
 */
public interface TermServices {

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
    public abstract GenericTermFactory getTermFactory();

}