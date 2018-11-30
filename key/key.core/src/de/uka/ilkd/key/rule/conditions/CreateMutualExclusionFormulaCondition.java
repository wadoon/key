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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Stores all the labels in the current program prefix pi in the given list SV.
 *
 * @author Dominic Steinhöfel
 */
public class CreateMutualExclusionFormulaCondition
        implements VariableCondition {
    private FormulaSV targetFormulaSV;
    private ArrayList<ProgramSV> participatingSVs = new ArrayList<>();
    private boolean done = false;

    public CreateMutualExclusionFormulaCondition() {
    }

    public void setTargetFormulaSV(FormulaSV targetFormulaSV) {
        this.targetFormulaSV = targetFormulaSV;
    }

    public void addSV(ProgramSV participatingSV) {
        participatingSVs.add(participatingSV);
    }

    @SuppressWarnings("rawtypes")
    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        if (done) {
            return matchCond;
        }

        final SVInstantiations svInst = matchCond.getInstantiations();

        final ArrayList<ProgramVariable> participatingVars = new ArrayList<>();
        for (ProgramSV psv : participatingSVs) {
            final Object inst = svInst.getInstantiation(psv);
            if (inst == null) {
                // Not yet fully instantiated
                return matchCond;
            }

            if (inst instanceof ProgramVariable) {
                participatingVars.add((ProgramVariable) inst);
            } else if (inst instanceof Iterable) {
                for (Object o : (Iterable) inst) {
                    participatingVars.add((ProgramVariable) o);
                }
            } else {
                throw new RuntimeException(
                    String.format("Unexpected instantiation type: %s",
                        inst.getClass().getSimpleName()));
            }
        }

        done = true;

        try {
            // svInst.getInstantiation(participatingSVs.get(0))
            final Term excIsNull = services.getTermBuilder().equals(
                services.getTermBuilder().var(participatingVars.get(0)),
                services.getTermBuilder().NULL());

            return matchCond.setInstantiations(
                svInst.add(targetFormulaSV, excIsNull, services));
        } catch (Throwable t) {
            return matchCond;
        }
    }

}
