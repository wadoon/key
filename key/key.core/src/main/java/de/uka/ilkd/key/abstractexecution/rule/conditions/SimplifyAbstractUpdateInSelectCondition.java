// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;

/**
 * @author Dominic Steinhoefel
 *
 */
public class SimplifyAbstractUpdateInSelectCondition implements VariableCondition {
    private final UpdateSV uSV;
    private final SchemaVariable oSV;
    private final SchemaVariable fSV;
    private final UpdateSV resultSV;

    public SimplifyAbstractUpdateInSelectCondition( //
            UpdateSV uSV, SchemaVariable oSV, SchemaVariable fSV, UpdateSV resultSV) {
        this.uSV = uSV;
        this.oSV = oSV;
        this.fSV = fSV;
        this.resultSV = resultSV;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions matchCond, Goal goal, Services services) {
        return null;
    }

    @Override
    public String toString() {
        return String.format("\\simplifyAbstractUpdateInSelect(%s, %s, %s, %s)", //
                uSV, oSV, fSV, resultSV);
    }

}
