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

package de.uka.ilkd.key.logic.op;

import org.key_project.common.core.logic.Name;

import de.uka.ilkd.key.logic.sort.Sort;


/**
 * Class of junctor operators, i.e., operators connecting
 * a given number of formula to create another formula. There
 * are six such operators: true, false, conjunction,
 * disjunction, negation, and implication.
 */
public final class Junctor extends AbstractSortedOperator {
   
    /** 
     * the true constant 
     */
    public static final Operator TRUE = new Junctor(new Name("true"),0);

    /** 
     * the false constant 
     */
    public static final Operator FALSE = new Junctor(new Name("false"),0);
    
    /** 
     * the usual 'and' operator '/\' (be A, B formulae then 'A /\ B'
     * is true if and only if A is true and B is true 
     */
    public static final Operator AND = new Junctor(new Name("and"),2);
    
    /** 
     * the usual 'or' operator '\/' (be A, B formulae then 'A \/ B'
     * is true if and only if A is true or B is true 
     */
    public static final Operator OR = new Junctor(new Name("or"),2);
    
    /** 
     * the usual 'negation' operator '-'
     */
    public static final Operator NOT = new Junctor(new Name("not"), 1);

    /**
     * the usual 'implication' operator '->' (be A, B formulae then
     * 'A -> B' is true if and only if A is false or B is true 
     */
    public static final Operator IMP = new Junctor(new Name("imp"),2);

    
    private static Sort[] createFormulaSortArray(int arity) {
	Sort[] result = new Sort[arity];
	for(int i = 0; i < arity; i++) {
	    result[i] = Sort.FORMULA;
	}
	return result;
    }
    
    
    private Junctor(Name name, int arity) {
	super(name, createFormulaSortArray(arity), Sort.FORMULA, true);
    }
}