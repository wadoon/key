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

import java.util.Optional;

import de.uka.ilkd.key.abstractexecution.java.AbstractProgramElement;
import de.uka.ilkd.key.abstractexecution.java.statement.AbstractStatement;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionContractUtils;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionContractUtils.AEFrameSpecs;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

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
    private final ProgramSV abstrProgSV;

    public InitializeParametricSkolemUpdate(SchemaVariable updateSV, ProgramSV abstrProgSV) {
        this.updateSV = updateSV;
        this.abstrProgSV = abstrProgSV;
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
        final Services services1 = services;

        final AEFrameSpecs accessibleAndAssignableClause = //
                AbstractExecutionContractUtils.getAccessibleAndAssignableLocsForNoBehaviorContract(
                        ape, matchCond.getMaybeSeqFor(), executionContext,
                        goal.getLocalSpecificationRepository(), services1);

        final Term update = tb.abstractUpdate(ape, accessibleAndAssignableClause.getAssignables(),
                accessibleAndAssignableClause.getAccesibles());
        
        // TODO (DS, 2020-05-18): Create different updates depending on flow specs 

        return matchCond.setInstantiations(svInst.add(this.updateSV, update, services));
    }

    @Override
    public String toString() {
        return String.format("\\varcond (\\initializeParametricSkolemUpdate(%s, %s))",
                this.updateSV, this.abstrProgSV);
    }
}