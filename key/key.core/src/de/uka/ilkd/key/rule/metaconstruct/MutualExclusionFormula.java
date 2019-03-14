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

package de.uka.ilkd.key.rule.metaconstruct;

import java.util.ArrayList;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Term transformer accepting a sequence of program variables and/or list of
 * program variables and creating a formula asserting that either none of these
 * variables "holds" (hold means being true for a boolean or non-null for an
 * Object variable, and has no meaning otherwise) or exactly one of those holds.
 *
 * This class only is abstract because the number of arguments needs to be fixed
 * beforehand; therefore, we create several such transformers for different
 * argument sizes.
 *
 * @author Dominic Steinhoefel
 */
public abstract class MutualExclusionFormula extends AbstractTermTransformer {

    public MutualExclusionFormula(int numArgs) {
        super(new Name("#mutualExclusionFormula" + numArgs), numArgs);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final ArrayList<ProgramVariable> participatingVars = new ArrayList<>();
        for (Term t : term.subs()) {
            if (t.op() instanceof ProgramVariable) {
                participatingVars.add((ProgramVariable) t.op());
            } else if (t.op() instanceof ProgramSV) {
                if (((ProgramSV) t.op()).isListSV()) {
                    @SuppressWarnings({ "rawtypes", "unchecked" })
                    final ImmutableArray<ProgramVariable> instantiation = //
                            (ImmutableArray) svInst
                                    .getInstantiation((ProgramSV) t.op());
                    assert instantiation != null;
                    participatingVars.addAll(
                        instantiation.stream().collect(Collectors.toList()));
                } else {
                    final ProgramVariable instantiation = (ProgramVariable) svInst
                            .getInstantiation((ProgramSV) t.op());
                    assert instantiation != null;
                    participatingVars.add(instantiation);
                }
            }
        }

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

        return result;
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