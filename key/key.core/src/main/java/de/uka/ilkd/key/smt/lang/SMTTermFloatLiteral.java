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

/** 
 * Created on: Aug 15, 2011
 */
package de.uka.ilkd.key.smt.lang;


public class SMTTermFloatLiteral extends SMTTerm {

	private final String value;
	private final SMTSort sort;
	
	public SMTTermFloatLiteral (String fpString){
		this.value = fpString;
		this.sort = SMTSort.FLOAT;
	}

	public SMTTermFloatLiteral (String fpString, SMTSort sort){
		this.value = fpString;
		this.sort = sort;
	}

	/** {@inheritDoc} */
	@Override
	public SMTSort sort () {
		return this.sort;
	}

	/** {@inheritDoc} */
	@Override
	public boolean occurs(SMTTermVariable a) {
		return false;
	}

	/** {@inheritDoc} */
	@Override
	public boolean occurs(String id) {
		return false;
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm substitute(SMTTermVariable a, SMTTerm b) {
		return this;
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm substitute(SMTTerm a, SMTTerm b) {
		return this;
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm replace(SMTTermCall a, SMTTerm b) {
		return this;
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm instantiate (SMTTermVariable a, SMTTerm b) {
		return this;
	}
	
	@Override
	public SMTTermFloatLiteral copy () {
		return new SMTTermFloatLiteral(value);
	}
	
	public String toSting (){
		return toString(0);
	}
	/** {@inheritDoc} */
	public String toString(int nestPos) {
		StringBuffer tab =  new StringBuffer();
		for(int i = 0; i< nestPos; i++) {
			tab = tab.append(" ");
		}
		
		return tab + value;
	}
	
	@Override
	public boolean equals (Object term) {
		
		if (term == null)
			return false;
		
		if (this == term)
			return true;
		
		if (! (term instanceof SMTTermFloatLiteral))
			return false;
		SMTTermFloatLiteral tn = (SMTTermFloatLiteral) term;
		
		return this.sort == tn.sort && this.value == tn.value;
	}
	
	@Override
	public int hashCode() {
		return value.hashCode();
	}

}