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
 * Created on: Dec 7, 2014
 */
package de.uka.ilkd.key.smt.lang;


public class SMTTermConst extends SMTTerm {
  
    private final SMTSort sort;
    private final String translation;

    public static final SMTTermConst FP_RNE =
	new SMTTermConst(SMTSort.FLOAT, "RNE");

    public SMTTermConst(SMTSort sort, String translation) {
	this.sort = sort;
	this.translation = translation;
    }

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
    public SMTSort sort() {
	return sort;
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
    public SMTTerm instantiate(SMTTermVariable a, SMTTerm b) {
	return this;
    }

    @Override
    public SMTTerm copy() {
	return this;
    }

    @Override
    public String toString() {
	return translation;
    }

    @Override
    public String toString(int nestPos) {
	StringBuffer tab = new StringBuffer();
	for (int i = 0; i < nestPos; i++) {
	    tab = tab.append(" ");
	}

	return tab + translation;
    }
}
