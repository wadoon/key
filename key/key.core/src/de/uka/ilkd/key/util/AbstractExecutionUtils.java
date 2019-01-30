package de.uka.ilkd.key.util;

import java.util.LinkedHashSet;
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
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.BlockContract;

/**
 * Utility functions for abtract execution.
 *
 * @author Dominic Steinhoefel
 */
public class AbstractExecutionUtils {
    /**
     * Returns the assignable {@link Operator}s (i.e. {@ProgramVariable}s and
     * Skolem location sets) of the "right" no-behavior contract for the given
     * {@link AbstractPlaceholderStatement}.
     *
     * @param aps
     *            The {@link AbstractPlaceholderStatement} for which to return
     *            the assignable {@link Operator}s.
     * @param context
     *            The context program (for choosing the "right" contract).
     * @param services
     *            The {@link Services} object.
     * @return The accessible {@link Operator}s for the given
     *         {@link AbstractPlaceholderStatement}.
     */
    public static List<Operator> getAccessibleOpsForNoBehaviorContract(
            AbstractPlaceholderStatement aps, ProgramElement context,
            Services services) {
        final Term assignableTerm = AbstractExecutionUtils
                .getAccessibleAndAssignableTermsForNoBehaviorContract(aps,
                        context, services).first;
        final Sort locSetSort = //
                services.getTypeConverter().getLocSetLDT().targetSort();

        final OpCollector opColl = new OpCollector();
        assignableTerm.execPostOrder(opColl);
        return opColl.ops().stream()
                .filter(op -> op instanceof ProgramVariable
                        || (op instanceof Function && op.arity() == 0
                                && ((Function) op).sort() == locSetSort))
                .collect(Collectors.toList());
    }

    /**
     * Returns the accessible {@ProgramVariable}s of the "right" no-behavior
     * contract for the given {@link AbstractPlaceholderStatement}.
     *
     * @param aps
     *            The {@link AbstractPlaceholderStatement} for which to return
     *            the accessible {@link ProgramVariable}s.
     * @param context
     *            The context program (for choosing the "right" contract).
     * @param services
     *            The {@link Services} object.
     * @return The accessible {@link ProgramVariable}s for the given
     *         {@link AbstractPlaceholderStatement}.
     */
    public static List<ProgramVariable> getAccessibleProgVarsForNoBehaviorContract(
            AbstractPlaceholderStatement aps, ProgramElement context,
            Services services) {
        return getAccessibleOpsForNoBehaviorContract(aps, context, services)
                .stream().filter(op -> op instanceof ProgramVariable)
                .map(ProgramVariable.class::cast).collect(Collectors.toList());
    }

    /**
     * Returns the assignable {@link Operator}s (i.e. {@ProgramVariable}s and
     * Skolem location sets) of the "right" no-behavior contract for the given
     * {@link AbstractPlaceholderStatement}.
     *
     * @param aps
     *            The {@link AbstractPlaceholderStatement} for which to return
     *            the assignable {@link Operator}s.
     * @param context
     *            The context program (for choosing the "right" contract).
     * @param services
     *            The {@link Services} object.
     * @return The assignable {@link Operator}s for the given
     *         {@link AbstractPlaceholderStatement}.
     */
    public static List<Operator> getAssignableOpsForNoBehaviorContract(
            AbstractPlaceholderStatement aps, ProgramElement context,
            Services services) {
        final Term assignableTerm = AbstractExecutionUtils
                .getAccessibleAndAssignableTermsForNoBehaviorContract(aps,
                        context, services).second;
        final Sort locSetSort = //
                services.getTypeConverter().getLocSetLDT().targetSort();

        final OpCollector opColl = new OpCollector();
        assignableTerm.execPostOrder(opColl);
        return opColl.ops().stream()
                .filter(op -> op instanceof ProgramVariable
                        || (op instanceof Function && op.arity() == 0
                                && ((Function) op).sort() == locSetSort))
                .collect(Collectors.toList());
    }

    /**
     * Returns the assignable {@ProgramVariable}s of the "right" no-behavior
     * contract for the given {@link AbstractPlaceholderStatement}.
     *
     * @param aps
     *            The {@link AbstractPlaceholderStatement} for which to return
     *            the assignable {@link ProgramVariable}s.
     * @param context
     *            The context program (for choosing the "right" contract).
     * @param services
     *            The {@link Services} object.
     * @return The assignable {@link ProgramVariable}s for the given
     *         {@link AbstractPlaceholderStatement}.
     */
    public static List<ProgramVariable> getAssignableProgVarsForNoBehaviorContract(
            AbstractPlaceholderStatement aps, ProgramElement context,
            Services services) {
        return getAssignableOpsForNoBehaviorContract(aps, context, services)
                .stream().filter(op -> op instanceof ProgramVariable)
                .map(ProgramVariable.class::cast).collect(Collectors.toList());
    }

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
     * for the current program context. Note that the current implementation is
     * quite ad-hoc.
     *
     * @param contracts
     *            The list of contracts for the placeholder statement.
     * @param contextProgram
     *            The context program (for choosing the right contract).
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
        final ProgramVariableCollector pvColl = //
                new ProgramVariableCollector(contextProgram, services);
        pvColl.start();
        return findRightContract(contracts, pvColl.result(), heap, services);
    }

    /**
     * Selects, amongst a given list of {@link BlockContract}s, the matching one
     * for the current context. Note that the current implementation is quite
     * ad-hoc (see inlined TODO). The principle is that the contract with most
     * variables in common (that is actually, the least number of variables NOT
     * in common) with the given set of context variables
     * <code>surroundingVars</code> will be selected. In case of a draw, the
     * first one wins.
     *
     * @param contracts
     *            The list of contracts for the placeholder statement.
     * @param contextProgram
     *            The context program (for choosing the right contract).
     * @param heap
     *            The heap term.
     * @param services
     *            The services object.
     * @return The most suitable {@link BlockContract} of the list. Will return
     *         null iff the given contracts list is empty.
     */
    public static BlockContract findRightContract(
            final List<BlockContract> contracts,
            final Set<LocationVariable> surroundingVars,
            final LocationVariable heap, Services services) {
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
            int varsNotInContext = Integer.MAX_VALUE;
            for (BlockContract bc : contracts) {
                final OpCollector opColl = new OpCollector();
                bc.getAccessibleClause(heap).execPostOrder(opColl);
                bc.getAssignable(heap).execPostOrder(opColl);
                bc.getAssignableNot(heap).execPostOrder(opColl);
                final int currVarsNotInContext = (int) opColl.ops().stream()
                        .filter(op -> op instanceof LocationVariable)
                        .map(LocationVariable.class::cast)
                        .filter(pv -> !surroundingVars.contains(pv)).count();
                if (currVarsNotInContext < varsNotInContext) {
                    varsNotInContext = currVarsNotInContext;
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
     * @param contextProgram
     *            TODO
     * @param services
     *            The {@link Services} object.
     * @return A pair of (1) the accessible and (2) the assignable clause for
     *         the {@link AbstractPlaceholderStatement}.
     */
    public static Pair<Term, Term> getAccessibleAndAssignableTermsForNoBehaviorContract(
            final AbstractPlaceholderStatement abstrStmt,
            final ProgramElement contextProgram, final Services services) {
        final ProgramVariableCollector pvColl = //
                new ProgramVariableCollector(contextProgram, services);
        pvColl.start();
        return getAccessibleAndAssignableTermsForNoBehaviorContract(abstrStmt,
                pvColl.result(), services);
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
     * @param surroundingVars
     *            TODO
     * @param services
     *            The {@link Services} object.
     * @return A pair of (1) the accessible and (2) the assignable clause for
     *         the {@link AbstractPlaceholderStatement}.
     */
    public static Pair<Term, Term> getAccessibleAndAssignableTermsForNoBehaviorContract(
            final AbstractPlaceholderStatement abstrStmt,
            final Set<LocationVariable> surroundingVars,
            final Services services) {
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

            final BlockContract contract = findRightContract(contracts,
                    surroundingVars, heap, services);

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
    public static Pair<Term, Term> getAccessibleAndAssignableTermsForNoBehaviorContract(
            final AbstractPlaceholderStatement abstrStmt,
            final MatchConditions matchCond, final Services services) {
        final Set<LocationVariable> surroundingVars = new LinkedHashSet<>();
        final ProgramVariableCollector pvc = //
                new ProgramVariableCollector(matchCond.getInstantiations()
                        .getContextInstantiation().contextProgram(), services);
        pvc.start();
        surroundingVars.addAll(pvc.result());
        matchCond.getMaybeSeqFor().ifPresent(sf -> {
            /*
             * NOTE (DS, 2019-01-30): Here, we just could use a
             * TermProgramVariableCollector and thus also consider PVs in the
             * programs. However, those might arise from one of the multiple
             * contracts with differently named versions. In those cases, we
             * prefer, in case of name collisions, those PVs that occur in
             * terms.
             */
            final OpCollector opColl = new OpCollector();
            sf.formula().execPostOrder(opColl);
            final Set<LocationVariable> result = opColl.ops().stream()
                    .filter(op -> op instanceof LocationVariable)
                    .map(LocationVariable.class::cast)
                    .collect(Collectors.toSet());
            surroundingVars.removeIf(lv1 -> result.stream()
                    .anyMatch(lv2 -> lv1.toString().equals(lv2.toString())));
            surroundingVars.addAll(result);
        });

        return getAccessibleAndAssignableTermsForNoBehaviorContract(abstrStmt,
                surroundingVars, services);
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
