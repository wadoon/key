// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.logic.Term;

/**
 *
 */
public interface ClassInvariant extends SpecificationElement {

    /**
     * Returns the invariant formula without implicit all-quantification over
     * the receiver object.
     */
    Term getOriginalInv();

    /**
     * returns the name of the class to which the invariant belongs
     */
    String getClassName();
}
