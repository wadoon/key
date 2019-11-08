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

import java.util.List;
import java.util.Optional;

import org.key_project.util.collection.UniqueArrayList;

import de.uka.ilkd.key.abstractexecution.java.AbstractProgramElement;
import de.uka.ilkd.key.abstractexecution.java.statement.AbstractStatement;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.HasToLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionContractUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Pair;

/**
 * Instantiates a parametric skolem update for abstract execution. The update
 * receives two LocSets for its assignable and accessible locations; those are
 * obtained from the block contracts of the {@link AbstractStatement} it is
 * generated for.
 *
 * @author Dominic Steinhoefel
 */
public class InitializeParametricSkolemUpdate implements VariableCondition {
    private final SchemaVariable updateSV;
    private final Optional<ProgramSV> maybeLhsSV; // for abstract expressions
    private final ProgramSV abstrProgSV;

    public InitializeParametricSkolemUpdate(SchemaVariable updateSV, ProgramSV abstrProgSV) {
        this.updateSV = updateSV;
        this.abstrProgSV = abstrProgSV;
        this.maybeLhsSV = Optional.empty();
    }

    public InitializeParametricSkolemUpdate(SchemaVariable updateSV, ProgramSV lhsSV,
            ProgramSV abstrProgSV) {
        this.updateSV = updateSV;
        this.abstrProgSV = abstrProgSV;
        this.maybeLhsSV = Optional.of(lhsSV);
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Goal goal, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        final Optional<ExecutionContext> executionContext = Optional
                .ofNullable(svInst.getExecutionContext());

        if (svInst.isInstantiated(this.updateSV)) {
            return matchCond;
        }

        final AbstractProgramElement ape = //
                (AbstractProgramElement) svInst.getInstantiation(this.abstrProgSV);

        final TermBuilder tb = services.getTermBuilder();

        final Pair<List<AbstractUpdateLoc>, UniqueArrayList<AbstractUpdateLoc>> accessibleAndAssignableClause = //
                AbstractExecutionContractUtils.getAccessibleAndAssignableTermsForNoBehaviorContract(
                        ape, matchCond.getMaybeSeqFor(), goal.getLocalSpecificationRepository(), services,
                        executionContext);

        final UniqueArrayList<AbstractUpdateLoc> assignables = accessibleAndAssignableClause.second;

        maybeLhsSV.map(svInst::getInstantiation).map(LocationVariable.class::cast).map(PVLoc::new)
                .map(HasToLoc::new).ifPresent(assignables::add);

        final Term update = tb.abstractUpdate(ape, assignables,
                accessibleAndAssignableClause.first);

        return matchCond.setInstantiations(svInst.add(this.updateSV, update, services));
    }

    @Override
    public String toString() {
        return maybeLhsSV
                .map(lhsSv -> String.format(
                        "\\varcond (\\initializeParametricSkolemUpdate(%s, %s, %s))", this.updateSV,
                        lhsSv, this.abstrProgSV))
                .orElse(String.format("\\varcond (\\initializeParametricSkolemUpdate(%s, %s))",
                        this.updateSV, this.abstrProgSV));
    }
}
