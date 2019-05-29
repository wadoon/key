// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Stores all the labels in the current program prefix pi in the given list SV.
 *
 * @author Dominic Steinhoefel
 */
public class PrefixContainsElementCondition implements VariableCondition {
    private final String className;
    private final boolean negated;

    public PrefixContainsElementCondition(String className, boolean negated) {
        this.className = className;
        this.negated = negated;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        ProgramPrefix prefix = //
                (ProgramPrefix) svInst.getContextInstantiation()
                        .contextProgram();
        do {
            if (prefix.getClass().getSimpleName().equals(className)) {
                return negated ? null : matchCond;
            }
        }
        while (prefix.hasNextPrefixElement()
                && (prefix = prefix.getNextPrefixElement()) != null);

        return negated ? matchCond : null;
    }

    @Override
    public String toString() {
        return String.format("%s\\varcond (\\prefixContainsElement(\"%s\"))",
                negated ? "\\not " : "", className);
    }
}
