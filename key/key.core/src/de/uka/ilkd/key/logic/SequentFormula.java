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

import org.key_project.common.core.logic.calculus.GenericSequentFormula;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.SourceElement;

/** 
 * A sequent formula is a wrapper around a formula that occurs 
 * as top level formula in a sequent. SequentFormula instances have
 * to be unique in the sequent as they are used by PosInOccurrence 
 * to determine the exact position. In earlier KeY versions this class 
 * was called ConstrainedFormula as it was equipped with an additional 
 * constraints. It would be interesting to add more value to this class 
 * by providing a way to add additional annotations or to cache local information 
 * about the formula.
 */
public class SequentFormula extends GenericSequentFormula<SourceElement, NameAbstractionTable, JavaDLVisitor, JavaDLTerm> {

    /** creates a new SequentFormula 
     * @param term a JavaDLTerm of sort Sort.FORMULA
     */ 
    public SequentFormula(JavaDLTerm term) {
        super(term);
    }
}