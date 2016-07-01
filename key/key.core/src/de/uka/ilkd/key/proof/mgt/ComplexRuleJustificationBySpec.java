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

package de.uka.ilkd.key.proof.mgt;

import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.common.core.rule.RuleApp;

import de.uka.ilkd.key.java.JavaDLTermServices;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;


public class ComplexRuleJustificationBySpec implements ComplexRuleJustification {

    private Map<RuleApp<Term, Goal>, RuleJustificationBySpec> app2Just
        = new LinkedHashMap<RuleApp<Term, Goal>, RuleJustificationBySpec>();
   
        
    public boolean isAxiomJustification() {
        return false;
    }
    
    
    public RuleJustification getSpecificJustification(RuleApp<Term, Goal> app,
            JavaDLTermServices services) {
        RuleJustification result = app2Just.get(app);
        return result == null ? this : result;
    }
    
    
    public void add(RuleApp<Term, Goal> ruleApp, RuleJustificationBySpec just) {
	// assert !(just instanceof ComplexRuleJustification);
        app2Just.put(ruleApp, just);
    }
    
    @Override
    public String toString() {
        return "ComplexRuleJustificationBySpec[" + app2Just + "]";
    }
}