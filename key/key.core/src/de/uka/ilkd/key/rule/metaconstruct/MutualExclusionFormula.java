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
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
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
        final Sort booleanSort = //
                services.getTypeConverter().getBooleanLDT().targetSort();

        final ArrayList<Term> participatingTerms = new ArrayList<>();
        for (Term t : term.subs()) {
            if (t.op() instanceof ProgramVariable) {
                participatingTerms.add(t);
            }
            else if (t.op() instanceof ProgramSV) {
                if (((ProgramSV) t.op()).isListSV()) {
                    @SuppressWarnings({ "rawtypes", "unchecked" })
                    final ImmutableArray<ProgramVariable> instantiation = //
                            (ImmutableArray) svInst
                                    .getInstantiation((ProgramSV) t.op());
                    assert instantiation != null;
                    participatingTerms.addAll(instantiation.stream()
                            .map(tb::var).collect(Collectors.toList()));
                }
                else {
                    final ProgramVariable instantiation = (ProgramVariable) svInst
                            .getInstantiation((ProgramSV) t.op());
                    assert instantiation != null;
                    participatingTerms.add(tb.var(instantiation));
                }
            }
            else if (t.op() instanceof SchemaVariable) {
                final Object instantiation = svInst
                        .getInstantiation((ProgramSV) t.op());
                assert instantiation != null;
                if (instantiation instanceof Term
                        && ((Term) instantiation).sort() == booleanSort) {
                    participatingTerms.add(((Term) instantiation));
                }
            }
            else if (t.sort() == booleanSort) {
                participatingTerms.add(t);
            }
            else {
                // Unsupported type of operator
                return null;
            }
        }

        Term result = tb.tt();

        for (final Term t : participatingTerms) {
            result = tb.and(result, falseTerm(t, services));
        }

        for (int i = 0; i < participatingTerms.size(); i++) {
            Term subResult = tb.tt();
            for (int j = 0; j < participatingTerms.size(); j++) {
                if (i == j) {
                    subResult = tb.and(subResult,
                            trueTerm(participatingTerms.get(j), services));
                }
                else {
                    subResult = tb.and(subResult,
                            falseTerm(participatingTerms.get(j), services));
                }
            }
            result = tb.or(result, subResult);
        }

        return result;
    }

    private Term trueTerm(Term term, Services services) {
        return elementaryTruthTerm(term, false, services);
    }

    private Term falseTerm(Term term, Services services) {
        return elementaryTruthTerm(term, true, services);
    }

    private Term elementaryTruthTerm(Term term, boolean negate,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();
        if (term.sort().extendsTrans(services.getJavaInfo().objectSort())) {
            final Term result = tb.equals(term, tb.NULL());
            return negate ? result : tb.not(result); // that's correct!
        }
        else if (term.sort().equals(
                services.getTypeConverter().getBooleanLDT().targetSort())) {
            final Term result = tb.equals(term, tb.TRUE());
            return negate ? tb.not(result) : result;
        }
        else {
            throw new RuntimeException(String.format(
                    "Unexpected type %s, expected an Object type or boolean",
                    term.sort().name()));
        }
    }

}