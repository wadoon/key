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

package de.uka.ilkd.key.logic;

/** 
 * This class represents the succedent or antecendent part of a
 * sequent. It is more or less a list without duplicates and subsumed
 * formulas. This is ensured using method removeRedundancy. In future
 * versions it can be enhanced to do other simplifications. A sequent
 * and so a semisequent has to be immutable. 
 */
public class Semisequent extends GenericSemisequent implements Iterable<SequentFormula> {

    
}
