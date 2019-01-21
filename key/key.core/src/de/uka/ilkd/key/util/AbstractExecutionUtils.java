package de.uka.ilkd.key.util;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.BlockContract;

/**
 * Utility functions for abtract execution.
 *
 * @author Dominic Steinhoefel
 */
public class AbstractExecutionUtils {
    /**
     * Selects, amongst a given list of {@link BlockContract}s, the matching one
     * for the current context. Note that the current implementation is quite
     * ad-hoc (see inlined TODO in
     * {@link #findRightContract(List, ProgramElement, LocationVariable, Services)}).
     *
     * @param contracts
     *            The list of contracts for the placeholder statement.
     * @param svInst
     *            The {@link SVInstantiations}.
     * @param heap
     *            The heap term.
     * @param services
     *            The services object.
     * @return The most suitable {@link BlockContract} of the list. Will return
     *         null iff the given contracts list is empty.
     */
    public static BlockContract findRightContract(
            final List<BlockContract> contracts, final SVInstantiations svInst,
            final LocationVariable heap, Services services) {
        return findRightContract(contracts,
                svInst.getContextInstantiation().contextProgram(), heap,
                services);
    }

    /**
     * Selects, amongst a given list of {@link BlockContract}s, the matching one
     * for the current context. Note that the current implementation is quite
     * ad-hoc (see inlined TODO).
     *
     * @param contracts
     *            The list of contracts for the placeholder statement.
     * @param svInst
     *            The {@link SVInstantiations}.
     * @param heap
     *            The heap term.
     * @param services
     *            The services object.
     * @return The most suitable {@link BlockContract} of the list. Will return
     *         null iff the given contracts list is empty.
     */
    public static BlockContract findRightContract(
            final List<BlockContract> contracts,
            final ProgramElement contextProgram, final LocationVariable heap,
            Services services) {
        /*
         * TODO (DS, 2018-12-21): Choose the right contract! There is probably a
         * contract from the other branch with wrong renamings. We somehow have
         * to find the right one. Ideas: (1) Get all PVs from context and choose
         * the contract with most PVs in common, or (2) store a node ID for the
         * contract in ProgVarReplacer when replacing, such that we can get the
         * contract assigned to a node which is an ancestor of this one, or (3)
         * check the Goal-local namespaces such that we choose the contract for
         * which the locals are known. We could also make the contracts
         * goal-local somehow. Option (1) is the ugliest which also might fail,
         * but the other ones require more actions or passing through more
         * parameters wo this method.
         *
         * Below, there is a quick implementation of method (1).
         */

        BlockContract contract = null;
        if (contracts.size() > 1) {
            final ProgramVariableCollector pvColl = new ProgramVariableCollector(
                    contextProgram, services);
            pvColl.start();
            final Set<LocationVariable> varsInProg = pvColl.result();

            int varsNotInProg = Integer.MAX_VALUE;
            for (BlockContract bc : contracts) {
                final OpCollector opColl = new OpCollector();
                bc.getAccessibleClause(heap).execPostOrder(opColl);
                bc.getAssignable(heap).execPostOrder(opColl);
                bc.getAssignableNot(heap).execPostOrder(opColl);
                final int currVarsNotInProg = (int) opColl.ops().stream()
                        .filter(op -> op instanceof LocationVariable)
                        .map(LocationVariable.class::cast)
                        .filter(pv -> !varsInProg.contains(pv)).count();
                if (currVarsNotInProg < varsNotInProg) {
                    varsNotInProg = currVarsNotInProg;
                    contract = bc;
                }
            }
        }
        else {
            contract = contracts.iterator().next();
        }
        return contract;
    }

    /**
     * Extracts the accessible and assignable term for the given
     * {@link AbstractPlaceholderStatement} based on the current context from
     * the {@link SpecificationRepository}. The default for both is allLocs
     * (everything assignable and accessible).
     *
     * @param abstrStmt
     *            The {@link AbstractPlaceholderStatement} for which to extract
     *            the accessible and assignable clause.
     * @param svInst
     *            The current {@link SVInstantiations} (for the context).
     * @param services
     *            The {@link Services} object.
     * @return A pair of (1) the accessible and (2) the assignable clause for
     *         the {@link AbstractPlaceholderStatement}.
     */
    public static Pair<Term, Term> getAccessibleAndAssignableTerms(
            final AbstractPlaceholderStatement abstrStmt,
            final SVInstantiations svInst, final Services services) {
        final TermBuilder tb = services.getTermBuilder();

        Term accessibleClause;
        Term assignableClause;

        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();

        final List<BlockContract> contracts = //
                getNoBehaviorContracts(abstrStmt, services);

        if (contracts.isEmpty()) {
            accessibleClause = tb.func(locSetLDT.getAllLocs());
            assignableClause = tb.func(locSetLDT.getAllLocs());
        }
        else {
            final LocationVariable heap = services.getTypeConverter()
                    .getHeapLDT().getHeap();

            final BlockContract contract = findRightContract(contracts, svInst,
                    heap, services);

            accessibleClause = contract.getAccessibleClause(heap);
            assignableClause = contract.getAssignable(heap);

            /*
             * TODO (DS, 2018-12-21): At this point, we might have to check that
             * the accessibles are actually accessible...
             */
        }

        return new Pair<Term, Term>(accessibleClause, assignableClause);
    }

    /**
     * Returns the contracts for the given {@link AbstractPlaceholderStatement}.
     * This refers to the "standard" contracts, i.e. without any specific
     * behavior (like "exceptional_behavior" etc.).
     *
     * @param abstrStmt
     *            The {@link AbstractPlaceholderStatement} for which to return
     *            the contracts.
     * @param services
     *            The {@link Services} object.
     * @return All the contracts for the given
     *         {@link AbstractPlaceholderStatement}.
     */
    public static List<BlockContract> getNoBehaviorContracts(
            final AbstractPlaceholderStatement abstrStmt,
            final Services services) {
        return services.getSpecificationRepository()
                .getAbstractPlaceholderStatementContracts(abstrStmt).stream()
                .filter(contract -> contract.getBaseName()
                        .equals("JML block contract"))
                /*
                 * We exclude return_behavior etc. here, because from those
                 * contracts we only consider the precondition.
                 */
                .collect(Collectors.toList());
    }

}
