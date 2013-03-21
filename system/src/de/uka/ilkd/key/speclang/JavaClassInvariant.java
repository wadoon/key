// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;


/**
 * A class invariant. Objects of type ABSClassInvariant are an intermediate result
 * of the specification language front ends; ultimately, they give rise to 
 * instances of the ClassAxiom class (more precisely, of its subclasses 
 * RepresentsAxiom and PartialInvAxiom), through which class invariants are
 * actually used in proofs.
 */
public interface JavaClassInvariant extends ClassInvariant {


    /**
     * Tells whether the invariant is static (i.e., does not refer to a
     * receiver object).
     */
    public boolean isStatic();
        
    /**
     * Returns another class invariant like this one, except that it refers to the 
     * passed KeYJavaType.
     */    
    public ClassInvariant setKJT(KeYJavaType kjt);
}
