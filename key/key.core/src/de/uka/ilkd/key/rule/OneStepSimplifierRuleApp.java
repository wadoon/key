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

package de.uka.ilkd.key.rule;

import org.key_project.common.core.logic.calculus.PosInOccurrence;

import de.uka.ilkd.key.logic.Term;

public class OneStepSimplifierRuleApp extends DefaultBuiltInRuleApp {
    
    private OneStepSimplifier.Protocol protocol;

    protected OneStepSimplifierRuleApp(BuiltInRule builtInRule, PosInOccurrence<Term> pio) {
        super(builtInRule, pio);
    }

    /**
     * @return the protocol, may be <code>null</code>
     */
    public OneStepSimplifier.Protocol getProtocol() {
        return protocol;
    }

    /**
     * @param protocol the protocol to set
     */
    public void setProtocol(OneStepSimplifier.Protocol protocol) {
        this.protocol = protocol;
    }

}