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

package org.key_project.common.core.services;

import org.key_project.common.core.logic.GenericNamespaceSet;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public interface GenericProofServices {

    ProgramServices getProgramServices();

    <S extends ProgramServices> S getProgramServices(Class<S> clazz);

    /**
     * returns the namespaces for functions, predicates etc.
     * @return the proof specific namespaces
     */
    GenericNamespaceSet getNamespaces();

}
