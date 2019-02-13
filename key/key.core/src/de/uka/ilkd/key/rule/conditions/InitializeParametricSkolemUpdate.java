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
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.AbstractExecutionUtils;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

/**
 * Instantiates a parametric skolem update for abstract execution. The update
 * receives two LocSets for its assignable and accessible locations; those are
 * obtained from the block contracts of the {@link AbstractPlaceholderStatement}
 * it is generated for.
 *
 * @author Dominic Steinhöfel
 */
public class InitializeParametricSkolemUpdate implements VariableCondition {
    private final SchemaVariable updateSV;
    private final ProgramSV abstrProgSV;

    public InitializeParametricSkolemUpdate(SchemaVariable updateSV,
            ProgramSV abstrProgSV) {
        this.updateSV = updateSV;
        this.abstrProgSV = abstrProgSV;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        if (svInst.isInstantiated(this.updateSV)) {
            return matchCond;
        }

        final AbstractPlaceholderStatement abstrStmt = //
                (AbstractPlaceholderStatement) svInst
                        .getInstantiation(this.abstrProgSV);

        final TermBuilder tb = services.getTermBuilder();

        final Pair<Term, Term> accessibleAndAssignableClause = //
                AbstractExecutionUtils
                        .getAccessibleAndAssignableTermsForNoBehaviorContract(
                                abstrStmt, matchCond, services);
        final Term accessibleClause = accessibleAndAssignableClause.first;
        final Term assignableClause = //
                fixPVsInHasTo(accessibleAndAssignableClause.second, services);

        final Term update = //
                tb.abstractUpdate(abstrStmt, assignableClause,
                        accessibleClause);

        return matchCond
                .setInstantiations(svInst.add(this.updateSV, update, services));
    }

    /**
     * After reading in the specs, there are "hasTo(someProgramVariable)"
     * {@link Term}s in the assignable clauses, which should be
     * "hasTo(singletonPV(someProgramVariable))", but we don't want to bother
     * users with also having to add that. So we here perform the normalization
     * that at the end, the hasTo always contains a LocSet parameter and not
     * only a program variable.
     *
     * @param originalAssignable
     *            The original assignable {@link Term}.
     * @param services
     *            The {@link Services} object.
     * @return The normalized {@link Term}.
     */
    private static Term fixPVsInHasTo(Term originalAssignable,
            Services services) {
        final List<Term> resultElems = new ArrayList<>();
        final TermBuilder tb = services.getTermBuilder();
        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        final Function union = locSetLDT.getUnion();
        final Function hasTo = locSetLDT.getHasTo();

        final Set<Term> constituents = MiscTools
                .dissasembleSetTerm(originalAssignable, union);

        for (Term t : constituents) {
            if (t.op() == hasTo && t.sub(0).op() instanceof ProgramVariable) {
                resultElems.add(tb.hasTo(tb.singletonPV(t.sub(0))));
            } else {
                resultElems.add(t);
            }
        }

        return tb.union(resultElems);
    }

    @Override
    public String toString() {
        return String.format(
                "\\varcond (\\initializeParametricSkolemUpdate(%s, %s))",
                this.updateSV, this.abstrProgSV);
    }
}
