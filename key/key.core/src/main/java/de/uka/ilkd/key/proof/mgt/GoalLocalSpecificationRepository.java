// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.proof.mgt;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.function.UnaryOperator;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.abstractexecution.java.AbstractProgramElement;
import de.uka.ilkd.key.abstractexecution.java.expression.AbstractExpression;
import de.uka.ilkd.key.abstractexecution.java.statement.AbstractStatement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.util.Pair;

/**
 * Contains specification elements that are local to a {@link Goal}, primarily
 * because they are subject to program variable renaming taking place during
 * proof construction. Examples are block and loop contracts.
 *
 * @author Dominic Steinhoefel
 */
public class GoalLocalSpecificationRepository {
    /**
     * Dummy for classes like Java AST Walkers that generally need this, but not in
     * all situations.
     */
    public final static GoalLocalSpecificationRepository DUMMY_REPO = new GoalLocalSpecificationRepository();

    private final Map<Pair<LoopStatement, Integer>, LoopSpecification> loopInvs;
    private final Map<Pair<StatementBlock, Integer>, ImmutableSet<BlockContract>> blockContracts;
    private final Map<Pair<AbstractProgramElement, Integer>, ImmutableSet<BlockContract>> abstractProgramElementContracts;
    private final Map<Pair<StatementBlock, Integer>, ImmutableSet<LoopContract>> loopContracts;

    /**
     * A map relating each loop statement its starting line number and set of loop
     * contracts.
     */
    private final Map<Pair<LoopStatement, Integer>, ImmutableSet<LoopContract>> loopContractsOnLoops;

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    public GoalLocalSpecificationRepository() {
        this(new LinkedHashMap<>(), new LinkedHashMap<>(), new LinkedHashMap<>(),
                new LinkedHashMap<>(), new LinkedHashMap<>());
    }

    /**
     * Applies the specified operator to every contract in this repository.
     *
     * @param op       an operator.
     * @param services services.
     *
     * @see SpecificationElement#map(java.util.function.UnaryOperator, Services)
     */
    public void map(UnaryOperator<Term> op, Services services) {
        mapValues(loopInvs, op, services);
        mapValueSets(blockContracts, op, services);
        mapValueSets(loopContracts, op, services);
    }

    /**
     * Returns the registered loop invariant for the passed loop, or null.
     */
    public LoopSpecification getLoopSpec(LoopStatement loop) {
        final int line = loop.getStartPosition().getLine();
        Pair<LoopStatement, Integer> l = new Pair<LoopStatement, Integer>(loop, line);
        LoopSpecification inv = loopInvs.get(l);
        if (inv == null && line != -1) {
            l = new Pair<LoopStatement, Integer>(loop, -1);
            inv = loopInvs.get(l);
        }
        return inv;
    }

    /**
     * Copies a loop invariant from a loop statement to another. If the original
     * loop does not possess an invariant, none is set to the target. A possibly
     * existing old registration will be overwritten, a registration for the
     * original loop remains untouched.
     *
     * @param from the loop with the original contract
     * @param loop the loop for which the contract is to be copied
     */
    public void copyLoopInvariant(LoopStatement from, LoopStatement to) {
        LoopSpecification inv = getLoopSpec(from);
        if (inv != null) {
            inv = inv.setLoop(to);
            addLoopInvariant(inv);
        }
    }

    /**
     * Registers the passed loop invariant, possibly overwriting an older
     * registration for the same loop.
     */
    public void addLoopInvariant(final LoopSpecification inv) {
        final LoopStatement loop = inv.getLoop();
        final int line = loop.getStartPosition().getLine();
        Pair<LoopStatement, Integer> l = new Pair<LoopStatement, Integer>(loop, line);
        loopInvs.put(l, inv);
        if (line != -1) {
            l = new Pair<LoopStatement, Integer>(loop, -1);
            loopInvs.put(l, inv);
        }
    }

    public ImmutableSet<BlockContract> getAbstractProgramElementContracts(
            AbstractProgramElement ape) {
        final Pair<AbstractProgramElement, Integer> abstrStmtWithLineNo = new Pair<>(ape,
                ape.getStartPosition().getLine());
        final ImmutableSet<BlockContract> contracts = abstractProgramElementContracts
                .get(abstrStmtWithLineNo);
        return Optional.ofNullable(contracts).orElseGet(() -> DefaultImmutableSet.nil());
    }

    public ImmutableSet<BlockContract> getAbstractProgramElementContracts(String apeId) {
        return abstractProgramElementContracts.keySet().stream()
                .filter(stmt -> stmt.first.getId().equals(apeId)).findAny()
                .map(lineStmtPair -> abstractProgramElementContracts.get(lineStmtPair))
                .orElseGet(() -> DefaultImmutableSet.nil());
    }

    /**
     * Returns all block contracts for the specified block.
     *
     * @param block a block.
     * @return all block contracts for the specified block.
     */
    public ImmutableSet<BlockContract> getBlockContracts(StatementBlock block) {
        final Pair<StatementBlock, Integer> b = new Pair<StatementBlock, Integer>(block,
                block.getStartPosition().getLine());
        final ImmutableSet<BlockContract> contracts = blockContracts.get(b);
        return Optional.ofNullable(contracts).orElseGet(() -> DefaultImmutableSet.nil());
    }

    /**
     * Returns all loop contracts for the specified block.
     *
     * @param block a block.
     * @return all loop contracts for the specified block.
     */
    public ImmutableSet<LoopContract> getLoopContracts(StatementBlock block) {
        final Pair<StatementBlock, Integer> b = new Pair<StatementBlock, Integer>(block,
                block.getStartPosition().getLine());
        final ImmutableSet<LoopContract> contracts = loopContracts.get(b);
        if (contracts == null) {
            return DefaultImmutableSet.<LoopContract>nil();
        } else {
            return contracts;
        }
    }

    /**
     * Returns block contracts for according block statement and modality.
     *
     * @param block    the given block.
     * @param modality the given modality.
     * @param services The Services object (for adding functional contracts to
     *                 global repository)
     * @return
     */
    public ImmutableSet<BlockContract> getBlockContracts(final StatementBlock block,
            final Modality modality, Services services) {
        ImmutableSet<BlockContract> result = getBlockContracts(block);
        final Modality matchModality = getMatchModality(modality);
        for (BlockContract contract : result) {
            if (!contract.getModality().equals(matchModality) || (modality.transaction()
                    && !contract.isTransactionApplicable() && !contract.isReadOnly(services))) {
                result = result.remove(contract);
            }
        }
        return result;
    }

    public ImmutableSet<LoopContract> getLoopContracts(final StatementBlock block,
            final Modality modality, Services services) {
        ImmutableSet<LoopContract> result = getLoopContracts(block);
        final Modality matchModality = getMatchModality(modality);
        for (LoopContract contract : result) {
            if (!contract.getModality().equals(matchModality) || (modality.transaction()
                    && !contract.isTransactionApplicable() && !contract.isReadOnly(services))) {
                result = result.remove(contract);
            }
        }
        return result;
    }

    /**
     * Returns all loop contracts for the specified loop.
     *
     * @param loop a loop.
     * @return all loop contracts for the specified loop.
     */
    public ImmutableSet<LoopContract> getLoopContracts(LoopStatement loop) {
        final Pair<LoopStatement, Integer> b = new Pair<LoopStatement, Integer>(loop,
                loop.getStartPosition().getLine());
        final ImmutableSet<LoopContract> contracts = loopContractsOnLoops.get(b);
        if (contracts == null) {
            return DefaultImmutableSet.<LoopContract>nil();
        } else {
            return contracts;
        }
    }

    /**
     * Returns loop contracts for according loop statement and modality.
     *
     * @param loop     the given loop.
     * @param modality the given modality.
     * @param services The Services object (for adding functional contracts to
     *                 global repository)
     * @return the set of resulting loop statements.
     */
    public ImmutableSet<LoopContract> getLoopContracts(final LoopStatement loop,
            final Modality modality, Services services) {
        ImmutableSet<LoopContract> result = getLoopContracts(loop);
        final Modality matchModality = getMatchModality(modality);
        for (LoopContract contract : result) {
            if (!contract.getModality().equals(matchModality) || (modality.transaction()
                    && !contract.isTransactionApplicable() && !contract.isReadOnly(services))) {
                result = result.remove(contract);
            }
        }
        return result;
    }

    /**
     * Adds a new {@code BlockContract} and a new {@link FunctionalBlockContract} to
     * the repository.
     *
     * @param contract the {@code BlockContract} to add.
     * @param services The Services object (for adding functional contracts to
     *                 global repository)
     */
    public void addBlockContract(final BlockContract contract, Services services) {
        addBlockContract(contract, false, services);
    }

    /**
     * Adds a new {@code BlockContract} to the repository.
     *
     * @param contract              the {@code BlockContract} to add.
     * @param addFunctionalContract whether or not to add a new
     *                              {@link FunctionalBlockContract} based on
     *                              {@code contract}.
     * @param services              The Services object (for adding functional
     *                              contracts to global repository)
     */
    public void addBlockContract(final BlockContract contract, boolean addFunctionalContract,
            Services services) {
        final StatementBlock block = contract.getBlock();
        final Pair<StatementBlock, Integer> b = new Pair<>(block,
                block.getStartPosition().getLine());
        blockContracts.put(b, getBlockContracts(block).add(contract));

        handleAddForFakeAEBlock(contract, block);
        if (addFunctionalContract) {
            services.getSpecificationRepository().addContract(contract);
        }
    }

    /**
     * <p>
     * Removes a {@code BlockContract} from the repository.
     * </p>
     *
     * <p>
     * The associated {@link FunctionalBlockContract} is not removed.
     * </p>
     *
     * @param contract the {@code BlockContract} to remove.
     */
    public void removeBlockContract(final BlockContract contract) {
        final StatementBlock block = contract.getBlock();
        final Pair<StatementBlock, Integer> b = new Pair<StatementBlock, Integer>(block,
                block.getStartPosition().getLine());

        ImmutableSet<BlockContract> set = blockContracts.get(b);
        final ImmutableSet<BlockContract> newContractSet = set.remove(contract);
        blockContracts.put(b, newContractSet);
        handleRemoveForFakeAEBlock(contract, block);
    }

    /**
     * Adds a new {@code LoopContract} and a new {@link FunctionalLoopContract} to
     * the repository.
     *
     * @param contract the {@code LoopContract} to add.
     * @param services The Services object (for adding functional contracts to
     *                 global repository)
     */
    public void addLoopContract(final LoopContract contract, Services services) {
        addLoopContract(contract, false, services);
    }

    /**
     * Adds a new {@code LoopContract} to the repository.
     *
     * @param contract              the {@code LoopContract} to add.
     * @param addFunctionalContract whether or not to add a new
     *                              {@link FunctionalLoopContract} based on
     *                              {@code contract}.
     * @param services              The Services object (for adding functional
     *                              contracts to global repository).
     */
    public void addLoopContract(final LoopContract contract, boolean addFunctionalContract,
            Services services) {
        if (contract.isOnBlock()) {
            final StatementBlock block = contract.getBlock();
            final Pair<StatementBlock, Integer> b = new Pair<StatementBlock, Integer>(block,
                    block.getStartPosition().getLine());
            loopContracts.put(b, getLoopContracts(block).add(contract));
        } else {
            final LoopStatement loop = contract.getLoop();
            final Pair<LoopStatement, Integer> b = new Pair<LoopStatement, Integer>(loop,
                    loop.getStartPosition().getLine());
            loopContractsOnLoops.put(b, getLoopContracts(loop).add(contract));
        }

        if (addFunctionalContract) {
            services.getSpecificationRepository().addFunctionalLoopContract(contract);
        }
    }

    /**
     * <p>
     * Removes a {@code LoopContract} from the repository.
     * </p>
     *
     * <p>
     * The associated {@link FunctionalLoopContract} is not removed.
     * </p>
     *
     * @param contract the {@code LoopContract} to remove.
     */
    public void removeLoopContract(final LoopContract contract) {
        if (contract.isOnBlock()) {
            final StatementBlock block = contract.getBlock();
            final Pair<StatementBlock, Integer> b = new Pair<StatementBlock, Integer>(block,
                    block.getStartPosition().getLine());

            ImmutableSet<LoopContract> set = loopContracts.get(b);
            loopContracts.put(b, set.remove(contract));
        } else {
            final LoopStatement loop = contract.getLoop();
            final Pair<LoopStatement, Integer> b = new Pair<LoopStatement, Integer>(loop,
                    loop.getStartPosition().getLine());

            ImmutableSet<LoopContract> set = loopContractsOnLoops.get(b);
            loopContractsOnLoops.put(b, set.remove(contract));
        }
    }

    public void addSpecs(ImmutableSet<SpecificationElement> specs, Services services) {
        for (SpecificationElement spec : specs) {
            if (spec instanceof LoopSpecification) {
                addLoopInvariant((LoopSpecification) spec);
            } else if (spec instanceof BlockContract) {
                addBlockContract((BlockContract) spec, services);
            } else if (spec instanceof LoopContract) {
                addLoopContract((LoopContract) spec, services);

                /*
                 * For those spec types below, we don't do anything, as they belong to the realm
                 * of the global SpecificationRepository; we also don't want to raise an
                 * exception.
                 */
            } else if (spec instanceof Contract) {
            } else if (spec instanceof ClassInvariant) {
            } else if (spec instanceof InitiallyClause) {
            } else if (spec instanceof ClassAxiom) {
            } else if (spec instanceof MergeContract) {
            } else {
                assert false : "unexpected spec: " + spec + "\n(" + spec.getClass() + ")";
            }
        }
    }

    @Override
    public GoalLocalSpecificationRepository clone() {
        return new GoalLocalSpecificationRepository( //
                new LinkedHashMap<>(this.loopInvs), //
                new LinkedHashMap<>(blockContracts), //
                new LinkedHashMap<>(abstractProgramElementContracts), //
                new LinkedHashMap<>(loopContracts), //
                new LinkedHashMap<>(loopContractsOnLoops));
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private GoalLocalSpecificationRepository(
            Map<Pair<LoopStatement, Integer>, LoopSpecification> loopInvs,
            Map<Pair<StatementBlock, Integer>, ImmutableSet<BlockContract>> blockContracts,
            Map<Pair<AbstractProgramElement, Integer>, ImmutableSet<BlockContract>> abstractProgramElementContracts,
            Map<Pair<StatementBlock, Integer>, ImmutableSet<LoopContract>> loopContracts,
            Map<Pair<LoopStatement, Integer>, ImmutableSet<LoopContract>> loopContractsOnLoops) {
        this.loopInvs = loopInvs;
        this.blockContracts = blockContracts;
        this.abstractProgramElementContracts = abstractProgramElementContracts;
        this.loopContracts = loopContracts;
        this.loopContractsOnLoops = loopContractsOnLoops;
    }

    /**
     * For Abstract Execution, we hack our way into reusing the existing block
     * contract architecture by wrapping Abstract Program Elements into artificial
     * blocks. Here, we check whether it's such an artificial block, and if so,
     * register the actual contracts in which we're interested.
     * 
     * @param contract The contract.
     * @param block    The block to check.
     */
    private void handleAddForFakeAEBlock(final BlockContract contract, final StatementBlock block) {
        extractAPEFromArtificialBlock(block).ifPresent(ape -> {
            final Pair<AbstractProgramElement, Integer> abstrStmtWithLineNo = new Pair<>(ape,
                    ape.getStartPosition().getLine());
            abstractProgramElementContracts.put(abstrStmtWithLineNo,
                    getAbstractProgramElementContracts(ape).add(contract));
        });
    }

    /**
     * For Abstract Execution, we hack our way into reusing the existing block
     * contract architecture by wrapping Abstract Program Elements into artificial
     * blocks. Here, we check whether it's such an artificial block, and if so,
     * remove the contract from the APE contracts.
     * 
     * @param contract The contract.
     * @param block    The block to check.
     */
    private void handleRemoveForFakeAEBlock(final BlockContract contract,
            final StatementBlock block) {
        extractAPEFromArtificialBlock(block).ifPresent(ape -> {
            final Pair<AbstractProgramElement, Integer> abstrStmtWithLineNo = new Pair<>(ape,
                    ape.getStartPosition().getLine());
            abstractProgramElementContracts.put(abstrStmtWithLineNo,
                    getAbstractProgramElementContracts(ape).remove(contract));
        });
    }

    /**
     * If the given {@link StatementBlock} is an artificial block used in Abstract
     * Execution (see
     * {@link #handleAddForFakeAEBlock(BlockContract, StatementBlock)}, returns the
     * {@link AbstractProgramElement} in the block. Otherwise an empty
     * {@link Optional}.
     * 
     * @param block The block to check.
     * @return the {@link AbstractProgramElement} in the block, or an empty
     *         {@link Optional}.
     */
    private Optional<AbstractProgramElement> extractAPEFromArtificialBlock(
            final StatementBlock block) {
        if (block.getBody().size() == 1 && block.getBody().get(0) instanceof AbstractStatement) {
            return Optional.of((AbstractProgramElement) block.getBody().get(0));
        } else if (block.getBody().size() == 1 && block.getBody().get(0) instanceof CopyAssignment
                && ((CopyAssignment) block.getBody().get(0))
                        .getLastElement() instanceof AbstractExpression) {
            return Optional.of((AbstractProgramElement) ((CopyAssignment) block.getBody().get(0))
                    .getLastElement());
        } else {
            return Optional.empty();
        }
    }

    private static Modality getMatchModality(final Modality modality) {
        if (modality.transaction()) {
            return modality == Modality.DIA_TRANSACTION ? Modality.DIA : Modality.BOX;
        } else {
            return modality;
        }
    }

    /**
     * Helper for {@link #map(UnaryOperator, Services)}.
     *
     * @param map      a map.
     * @param op       an operator.
     * @param services services.
     */
    @SuppressWarnings("unchecked")
    private <K, V extends SpecificationElement> void mapValueSets(Map<K, ImmutableSet<V>> map,
            UnaryOperator<Term> op, Services services) {
        for (Entry<K, ImmutableSet<V>> entry : map.entrySet()) {
            final K key = entry.getKey();
            final ImmutableSet<V> oldSet = entry.getValue();
            ImmutableSet<V> newSet = DefaultImmutableSet.nil();

            for (V oldContract : oldSet) {
                V newContract = (V) oldContract.map(op, services);
                newSet = newSet.add(newContract);

//                assert oldContract.getName().equals(newContract.getName());
//                if (oldContract instanceof Contract
//                        && contractsByName.containsKey(oldContract.getName())) {
//                    contractsByName.put(oldContract.getName(), (Contract) newContract);
//                }
            }

            map.put(key, (ImmutableSet<V>) oldSet.stream()
                    .map(contract -> contract.map(op, services)).collect(ImmutableSet.collector()));
        }
    }

    /**
     * Helper for {@link #map(UnaryOperator, Services)}.
     *
     * @param map      a map.
     * @param op       an operator.
     * @param services services.
     */
    @SuppressWarnings("unchecked")
    private <K, V extends SpecificationElement> void mapValues(Map<K, V> map,
            UnaryOperator<Term> op, Services services) {
        for (Entry<K, V> entry : map.entrySet()) {
            final K key = entry.getKey();
            final V oldContract = entry.getValue();
            final V newContract = (V) oldContract.map(op, services);
            map.put(key, newContract);

//            assert oldContract.getName().equals(newContract.getName());
//            if (oldContract instanceof Contract
//                    && contractsByName.containsKey(oldContract.getName())) {
//                contractsByName.put(oldContract.getName(), (Contract) newContract);
//            }
        }
    }

}
