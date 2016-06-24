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

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.theories.CCTheory;

/**
 * Provides access to theories.
 *
 * @author Dominic Scheurer
 */
public interface CCTheoryServices {

    /**
     * TODO: Document.
     *
     * @param theoryName
     * @return
     */
    CCTheory getTheory(Name theoryName);
    
    /**
     * TODO: Document.
     *
     * @param sort
     * @return
     */
    CCTheory getTheoryFor(Sort sort);
    
    /**
     * TODO: Document.
     *
     * @return
     */
    Iterable<? extends CCTheory> getTheories();
    
}
