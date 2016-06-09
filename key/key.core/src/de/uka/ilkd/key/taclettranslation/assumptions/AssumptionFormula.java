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

package de.uka.ilkd.key.taclettranslation.assumptions;

import java.util.Collection;

import org.key_project.common.core.services.TermServices;

import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.IllegalTacletException;
import de.uka.ilkd.key.taclettranslation.TacletFormula;

public class AssumptionFormula implements TacletFormula {

    Taclet taclet;
    Collection<JavaDLTerm> formula;
    String status;
    TacletConditions conditions;

    public TacletConditions getConditions() {
	return conditions;
    }

    public AssumptionFormula(Taclet taclet, Collection<JavaDLTerm> formula,
	    String status)  {
	this.taclet = taclet;
	this.formula = formula;
	this.status = status;
    }
    
    

    public AssumptionFormula(Taclet taclet, Collection<JavaDLTerm> formula,
	    String status, TacletConditions conditions) throws IllegalTacletException {
	super();
	this.taclet = taclet;
	this.formula = formula;
	this.status = status;
	this.conditions = conditions == null ? new TacletConditions(taclet)
	        : conditions;

    }

    public JavaDLTerm getFormula(TermServices services) {
	return services.getTermBuilder().and(formula.toArray(new JavaDLTerm[formula.size()]));
	// return formula;
    }

    public Taclet getTaclet() {
	return taclet;
    }

    public String getStatus() {
	return status;
    }

    public Collection<JavaDLTerm> getInstantiations() {

	return formula;
    }

}