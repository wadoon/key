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

package de.uka.ilkd.key.abstractexecution.rule.conditions;

import java.util.Set;

import de.uka.ilkd.key.abstractexecution.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstrUpdateLHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstrUpdateRHS;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
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

        final Pair<Set<AbstrUpdateRHS>, Set<AbstrUpdateLHS>> accessibleAndAssignableClause = //
                AbstractExecutionUtils
                        .getAccessibleAndAssignableTermsForNoBehaviorContract(
                                abstrStmt, matchCond, services);

        final Term update = //
                tb.abstractUpdate(abstrStmt,
                        accessibleAndAssignableClause.second,
                        accessibleAndAssignableClause.first);

        return matchCond
                .setInstantiations(svInst.add(this.updateSV, update, services));
    }

    @Override
    public String toString() {
        return String.format(
                "\\varcond (\\initializeParametricSkolemUpdate(%s, %s))",
                this.updateSV, this.abstrProgSV);
    }
}
