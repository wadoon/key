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

import java.util.ArrayList;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.ProgramList;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Stores all the loop labels in the current program prefix pi in the given list
 * SV.
 *
 * @author Dominic Steinhoefel
 */
public class StoreContextLoopLabelsInCondition implements VariableCondition {
    private final ProgramSV labelsSV;

    public StoreContextLoopLabelsInCondition(ProgramSV labelsSV) {
        assert labelsSV.isListSV();
        this.labelsSV = labelsSV;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        final ArrayList<ProgramElement> labels = new ArrayList<>();
        ProgramPrefix prefix = //
                (ProgramPrefix) svInst.getContextInstantiation()
                        .contextProgram();
        do {
            if (prefix instanceof LabeledStatement
                    && ((LabeledStatement) prefix)
                            .getBody() instanceof LoopStatement) {
                labels.add(((LabeledStatement) prefix).getLabel());
            }
        }
        while (prefix.hasNextPrefixElement()
                && (prefix = prefix.getNextPrefixElement()) != null);

        ProgramList pl = new ProgramList(
                new ImmutableArray<ProgramElement>(labels));

        return matchCond.setInstantiations(svInst.add(labelsSV, pl, services));
    }

    @Override
    public String toString() {
        return String.format("\\varcond (\\storeContextLoopLabelsIn(%s))",
                labelsSV);
    }
}