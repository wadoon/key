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

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.JavaStatement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.BlockContractImpl;

/**
 * Checks whether the current statement represents a JML assume or assert
 * statement. This currently cannot be cleanly checked; instead, we return a
 * positive result if the annotated block is empty, but has a contract.
 *
 * @author Dominic Steinhoefel
 */
public class RepresentsAssumeOrAssertStmtCondition implements VariableCondition {
    private final boolean negated;

    public RepresentsAssumeOrAssertStmtCondition(boolean negated) {
        this.negated = negated;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Goal goal, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        final Modality modality = (Modality) svInst.lookupValue(new Name("#allmodal"));

        if (modality == null) {
            return null;
        }

        if (representsJMLAssumeOrAssertStmt(modality,
                svInst.getContextInstantiation().contextProgram(), goal)) {
            return negated ? null : matchCond;
        } else {
            return negated ? matchCond : null;
        }
    }

    /**
     * Checks if the given source element represents a JML assume or assert
     * statement. This currently cannot be cleanly checked; instead, we return a
     * positive result if the annotated block is empty, but has a contract.
     * 
     * @param modality The modality in which the source element appears.
     * @param element  The source element.
     * @param goal     The current goal.
     * @return True if the source element meets the conditions for representing a
     *         JML assume or assert statement.
     */
    private static boolean representsJMLAssumeOrAssertStmt(final Modality modality,
            final SourceElement element, final Goal goal) {
        final BlockContract contract = //
                getContractOfFirstStatementInPrefixWithAtLeastOneContract(modality, element, goal);

        if (contract == null) {
            return false;
        }

        return (contract.getBlock().isEmpty()
                || contract.getBlock().toString().replaceAll(" ", "").equals("{;}"));
    }

    /**
     *
     * @param modality the contract's modality.
     * @param element  the source element (first program prefix element).
     * @param goal     the current goal.
     * @return the first block in the java block's prefix with at least one
     *         applicable contract, or null.
     */
    private static BlockContract getContractOfFirstStatementInPrefixWithAtLeastOneContract(
            final Modality modality, final SourceElement element, final Goal goal) {
        if (!(element instanceof ProgramPrefix)) {
            return null;
        }

        ProgramPrefix prefix = (ProgramPrefix) element;
        while (prefix.hasNextPrefixElement()) {
            prefix = prefix.getNextPrefixElement();
        }

        if (!(prefix instanceof StatementBlock)) {
            return null;
        }

        final ImmutableSet<BlockContract> contracts = getApplicableContracts(
                (StatementBlock) prefix, modality, goal);

        if (contracts != null && contracts.size() > 0) {
            return BlockContractImpl.combine(contracts, goal.getLocalSpecificationRepository(),
                    goal.proof().getServices());
        }

        return null;
    }

    /**
     *
     * @param statement a block.
     * @param modality  the current goal's modality.
     * @param goal      the current goal.
     * @return all applicable block contracts for the block from the repository.
     */
    private static ImmutableSet<BlockContract> getApplicableContracts(final JavaStatement statement,
            final Modality modality, final Goal goal) {
        if (statement instanceof StatementBlock) {
            final GoalLocalSpecificationRepository specifications = goal
                    .getLocalSpecificationRepository();
            StatementBlock block = (StatementBlock) statement;

            final Services services = goal.proof().getServices();
            ImmutableSet<BlockContract> collectedContracts = specifications.getBlockContracts(block,
                    modality, services);
            if (modality == Modality.BOX) {
                collectedContracts = collectedContracts
                        .union(specifications.getBlockContracts(block, Modality.DIA, services));
            } else if (modality == Modality.BOX_TRANSACTION) {
                collectedContracts = collectedContracts.union(specifications
                        .getBlockContracts(block, Modality.DIA_TRANSACTION, services));
            }
            return collectedContracts;
        } else {
            return null;
        }
    }

    @Override
    public String toString() {
        return String.format("\\varcond (%s\\representsAssumeOrAssertStmt)",
                negated ? "\\not" : "");
    }
}