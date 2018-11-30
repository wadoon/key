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
import de.uka.ilkd.key.logic.TermBuilder;
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
            final TermBuilder tb = services.getTermBuilder();
            Term result = tb.tt();

            for (ProgramVariable pv : participatingVars) {
                result = tb.and(result, falseTerm(pv, services));
            }

            for (int i = 0; i < participatingVars.size(); i++) {
                Term subResult = tb.tt();
                for (int j = 0; j < participatingVars.size(); j++) {
                    if (i == j) {
                        subResult = tb.and(subResult,
                            trueTerm(participatingVars.get(j), services));
                    } else {
                        subResult = tb.and(subResult,
                            falseTerm(participatingVars.get(j), services));
                    }
                }
                result = tb.or(result, subResult);
            }

            return matchCond.setInstantiations(
                svInst.add(targetFormulaSV, result, services));
        } catch (Throwable t) {
            return matchCond;
        }
    }

    private Term trueTerm(ProgramVariable var, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        if (var.sort().extendsTrans(services.getJavaInfo().objectSort())) {
            return tb.not(tb.equals(tb.var(var), tb.NULL()));
        } else if (var.sort().equals(
            services.getTypeConverter().getBooleanLDT().targetSort())) {
            return tb.equals(tb.var(var), tb.TRUE());
        } else {
            throw new RuntimeException(String.format(
                "Unexpected type %s, expected an Object type or boolean",
                var.sort().name()));
        }
    }

    private Term falseTerm(ProgramVariable var, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        if (var.sort().extendsTrans(services.getJavaInfo().objectSort())) {
            return tb.equals(tb.var(var), tb.NULL());
        } else if (var.sort().equals(
            services.getTypeConverter().getBooleanLDT().targetSort())) {
            return tb.equals(tb.var(var), tb.FALSE());
        } else {
            throw new RuntimeException(String.format(
                "Unexpected type %s, expected an Object type or boolean",
                var.sort().name()));
        }
    }

}
