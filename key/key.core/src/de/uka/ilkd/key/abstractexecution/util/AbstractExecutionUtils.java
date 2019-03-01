package de.uka.ilkd.key.abstractexecution.util;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.abstractexecution.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstrUpdateLHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstrUpdateRHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AllLocsLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * Utility functions for abtract execution.
 *
 * @author Dominic Steinhoefel
 */
public class AbstractExecutionUtils {
    /**
     * Returns the accessible locations of the "right" no-behavior contract for
     * the given {@link AbstractPlaceholderStatement}.
     *
     * @param aps
     *            The {@link AbstractPlaceholderStatement} for which to return
     *            the accessible locations.
     * @param context
     *            The context program (for choosing the "right" contract).
     * @param services
     *            The {@link Services} object.
     * @return The accessible locations for the given
     *         {@link AbstractPlaceholderStatement}.
     */
    public static Set<AbstrUpdateRHS> getAccessibleTermsForNoBehaviorContract(
            AbstractPlaceholderStatement aps, ProgramElement context,
            Services services) {
        return AbstractExecutionUtils
                .getAccessibleAndAssignableTermsForNoBehaviorContract(aps,
                        context, services).first;
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
        return getAccessibleTermsForNoBehaviorContract(aps, context, services)
                .stream().filter(PVLoc.class::isInstance).map(PVLoc.class::cast)
                .map(PVLoc::childOp).map(ProgramVariable.class::cast)
                .collect(Collectors.toList());
    }

    /**
     * Returns the assignable locations of the "right" no-behavior contract for
     * the given {@link AbstractPlaceholderStatement}.
     *
     * @param aps
     *            The {@link AbstractPlaceholderStatement} for which to return
     *            the assignable locations.
     * @param context
     *            The context program (for choosing the "right" contract).
     * @param services
     *            The {@link Services} object.
     * @return The assignable locations for the given
     *         {@link AbstractPlaceholderStatement}.
     */
    public static Set<AbstrUpdateLHS> getAssignableOpsForNoBehaviorContract(
            AbstractPlaceholderStatement aps, ProgramElement context,
            Services services) {
        return AbstractExecutionUtils
                .getAccessibleAndAssignableTermsForNoBehaviorContract(aps,
                        context, services).second;
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
        } else {
            contract = contracts.iterator().next();
        }
        return contract;
    }

    /**
     * Extracts the accessible and assignable locations for the given
     * {@link AbstractPlaceholderStatement} based on the current context from
     * the {@link SpecificationRepository}. The default for both is allLocs
     * (everything assignable and accessible).
     *
     * @param abstrStmt
     *            The {@link AbstractPlaceholderStatement} for which to extract
     *            the accessible and assignable clause.
     * @param contextProgram
     *            The context program to determine the right contract (after
     *            renamings).
     * @param services
     *            The {@link Services} object.
     * @return A pair of (1) the accessible and (2) the assignable locations for
     *         the {@link AbstractPlaceholderStatement}.
     */
    public static Pair<Set<AbstrUpdateRHS>, Set<AbstrUpdateLHS>> getAccessibleAndAssignableTermsForNoBehaviorContract(
            final AbstractPlaceholderStatement abstrStmt,
            final ProgramElement contextProgram, final Services services) {
        final ProgramVariableCollector pvColl = //
                new ProgramVariableCollector(contextProgram, services);
        pvColl.start();
        return getAccessibleAndAssignableTermsForNoBehaviorContract(abstrStmt,
                pvColl.result(), Optional.empty(), services);
    }

    /**
     * Extracts the accessible and assignable locations for the given
     * {@link AbstractPlaceholderStatement} based on the current context from
     * the {@link SpecificationRepository}. The default for both is allLocs
     * (everything assignable and accessible).
     *
     * @param abstrStmt
     *            The {@link AbstractPlaceholderStatement} for which to extract
     *            the accessible and assignable clause.
     * @param surroundingVars
     *            {@link LocationVariable}s in the context to distinguish
     *            several contracts.
     * @param executionContext
     *            An {@link Optional} {@link ExecutionContext} -- make sure to
     *            actually pass one if you are interested in fields. Otherwise,
     *            only Skolem functions and program variables are considered.
     * @param services
     *            The {@link Services} object.
     * @return A pair of (1) the accessible and (2) the assignable locations for
     *         the {@link AbstractPlaceholderStatement}.
     */
    public static Pair<Set<AbstrUpdateRHS>, Set<AbstrUpdateLHS>> getAccessibleAndAssignableTermsForNoBehaviorContract(
            final AbstractPlaceholderStatement abstrStmt,
            final Set<LocationVariable> surroundingVars,
            Optional<ExecutionContext> executionContext,
            final Services services) {
        Set<AbstrUpdateRHS> accessibleClause;
        Set<AbstrUpdateLHS> assignableClause;

        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();

        final List<BlockContract> contracts = //
                getNoBehaviorContracts(abstrStmt, services);

        if (contracts.isEmpty()) {
            accessibleClause = Collections
                    .singleton(new AllLocsLoc(locSetLDT.getAllLocs()));
            assignableClause = Collections
                    .singleton(new AllLocsLoc(locSetLDT.getAllLocs()));
        } else {
            final LocationVariable heap = services.getTypeConverter()
                    .getHeapLDT().getHeap();

            final BlockContract contract = findRightContract(contracts,
                    surroundingVars, heap, services);

            accessibleClause = AbstractUpdateFactory.INSTANCE
                    .abstractUpdateLocsFromUnionTerm(
                            contract.getAccessibleClause(heap),
                            executionContext, services)
                    .stream().map(AbstrUpdateRHS.class::cast).collect(Collectors
                            .toCollection(() -> new LinkedHashSet<>()));
            assignableClause = AbstractUpdateFactory.INSTANCE
                    .abstractUpdateLocsFromUnionTerm(
                            contract.getAssignable(heap), executionContext,
                            services)
                    .stream().map(AbstrUpdateLHS.class::cast).collect(Collectors
                            .toCollection(() -> new LinkedHashSet<>()));
        }

        return new Pair<Set<AbstrUpdateRHS>, Set<AbstrUpdateLHS>>(
                accessibleClause, assignableClause);
    }

    /**
     * Extracts the accessible and assignable locations for the given
     * {@link AbstractPlaceholderStatement} based on the current context from
     * the {@link SpecificationRepository}. The default for both is allLocs
     * (everything assignable and accessible).
     *
     * @param abstrStmt
     *            The {@link AbstractPlaceholderStatement} for which to extract
     *            the accessible and assignable locations.
     * @param svInst
     *            The current {@link SVInstantiations} (for the context).
     * @param services
     *            The {@link Services} object.
     * @return A pair of (1) the accessible and (2) the assignable locations for
     *         the {@link AbstractPlaceholderStatement}.
     */
    public static Pair<Set<AbstrUpdateRHS>, Set<AbstrUpdateLHS>> getAccessibleAndAssignableTermsForNoBehaviorContract(
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
                surroundingVars,
                Optional.of(
                        matchCond.getInstantiations().getExecutionContext()),
                services);
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

    /**
     * Returns {@link Term}s of the RHS of an {@link AbstractUpdate} term.
     *
     * @param update
     *            The {@link AbstractUpdate} {@link Term} for which to return
     *            the accessibles.
     * @param tb
     *            The {@link TermBuilder}, needed for disassembling the update
     *            {@link Term}.
     * @return All {@link Term}s in the RHS of an {@link AbstractUpdate} term.
     */
    public static Set<Term> getAccessiblesForAbstractUpdate(Term update,
            TermBuilder tb) {
        assert update.op() instanceof AbstractUpdate;
        assert update.arity() == 1;

        return tb.setUnionToSet(update.sub(0));
    }

    /**
     * Computes the sets of assigned-before-used and used-before-assigned
     * operators in the target term. In case of a conflict, i.e. in one subterm
     * an operator is used before assigned and in the other vice versa, used
     * before assigned always wins. The returned pair consists of the
     * assigned-before-used set as first and the used-before-assigned set as
     * second element. The two sets are disjunct.
     *
     * @param target
     *            The term for which to analyze the assigned-before-used
     *            relationships.
     * @param ec
     *            The {@link ExecutionContext}, for handling fields.
     * @param services
     *            The {@link Services} object.
     * @return (1) assigned-before-used and (2) used-before-assigned operators.
     *         Sets are ordered. May be an empty optional if there is a
     *         construct not (yet) supported, in this case, the condition should
     *         not be applicable.
     */
    public static Optional<Pair<Set<AbstrUpdateRHS>, Set<AbstrUpdateRHS>>> opsAssignedBeforeUsed(
            Term target, ExecutionContext ec, Services services) {
        final Set<AbstrUpdateRHS> assignedBeforeUsed = new LinkedHashSet<>();
        final Set<AbstrUpdateRHS> usedBeforeAssigned = new LinkedHashSet<>();
        final AbstractUpdateFactory factory = AbstractUpdateFactory.INSTANCE;

        Optional<AbstractUpdateLoc> loc = factory
                .tryExtractAbstrUpdateLocFromTerm(target, ec, services);
        if (loc.isPresent()) {
            usedBeforeAssigned.add((AbstrUpdateRHS) loc.get());
        }

        // Update applications -- those are most interesting
        else if (target.op() == UpdateApplication.UPDATE_APPLICATION) {
            final Term update = target.sub(0);
            final Term updateTarget = target.sub(1);

            // Update in sequential normal form
            if (MergeRuleUtils.isUpdateNormalForm(update)) {
                final List<Term> elems = MergeRuleUtils
                        .getElementaryUpdates(update);

                for (final Term elem : elems) {
                    final AbstrUpdateRHS lhs = new PVLoc(
                            (LocationVariable) ((ElementaryUpdate) elem.op())
                                    .lhs());
                    final Term rhs = elem.sub(0);
                    loc = factory.tryExtractAbstrUpdateLocFromTerm( //
                            rhs, ec, services);
                    if (loc.isPresent()) {
                        if (!assignedBeforeUsed.contains(loc.get())) {
                            usedBeforeAssigned.add((AbstrUpdateRHS) loc.get());
                        }
                    }

                    if (!usedBeforeAssigned.contains(lhs)) {
                        assignedBeforeUsed.add(lhs);
                    }
                }
            }

            // Abstract Update
            else if (update.op() instanceof AbstractUpdate) {
                opsHaveToAssignBeforeUsedForAbstrUpd(update, assignedBeforeUsed,
                        usedBeforeAssigned, ec, services);
            }

            // Concatenated abstract update
            else if (update.op() == UpdateJunctor.CONCATENATED_UPDATE) {
                final List<Term> abstractUpdateTerms = //
                        abstractUpdatesFromConcatenation(update);
                for (Term abstrUpdTerm : abstractUpdateTerms) {
                    opsHaveToAssignBeforeUsedForAbstrUpd(abstrUpdTerm,
                            assignedBeforeUsed, usedBeforeAssigned, ec,
                            services);
                }
            }

            // Something else -- ignore for now, exit (completeness relevant)
            else {
                // Probably a nested application
                return Optional.empty();
            }

            final Pair<Set<AbstrUpdateRHS>, Set<AbstrUpdateRHS>> subResult = //
                    opsAssignedBeforeUsed(updateTarget, ec, services)
                            .orElse(null);

            if (subResult == null) {
                return Optional.empty();
            }

            usedBeforeAssigned.addAll(subResult.second.stream()
                    .filter(op -> !assignedBeforeUsed.contains(op))
                    .collect(Collectors.toSet()));

            assignedBeforeUsed.addAll(subResult.first.stream()
                    .filter(op -> !usedBeforeAssigned.contains(op))
                    .collect(Collectors.toSet()));
        }

        else if (target.op() instanceof Modality) {
            /*
             * TODO (DS, 2019-02-01): Use some existing collector for programs.
             */
            return Optional.empty();
        }

        // Any other term
        else {
            for (final Term sub : target.subs()) {
                final Pair<Set<AbstrUpdateRHS>, Set<AbstrUpdateRHS>> subResult = //
                        opsAssignedBeforeUsed(sub, ec, services).orElse(null);

                if (subResult == null) {
                    return Optional.empty();
                }

                /* Add all "used before assigned" */
                usedBeforeAssigned.addAll(subResult.second);

                /* Add all "assigned before used" */
                assignedBeforeUsed.addAll(subResult.first);

                /*
                 * Now, remove those from "assigned before used" that are used
                 * before assigned. Take that term as example:
                 *
                 * {U}({x:=y}phi & (psi(x)))
                 *
                 * Here, x should be used before assigned and not assigned
                 * before used. Therefore the removal.
                 */
                assignedBeforeUsed.removeAll(usedBeforeAssigned);
            }
        }

        /*
         * At the end, all operators that are assigned before used should not be
         * in the used before assigned set.
         */
        assert assignedBeforeUsed.stream()
                .noneMatch(usedBeforeAssigned::contains);

        /* Also vice versa */
        assert usedBeforeAssigned.isEmpty() || usedBeforeAssigned.stream()
                .noneMatch(assignedBeforeUsed::contains);

        return Optional.of(new Pair<>(assignedBeforeUsed, usedBeforeAssigned));
    }

    /**
     * Calculates for an abstract update which operators in it are "have-to"
     * assigned before used. The "maybe" assignables are ignored! The current
     * use case is to drop assignables in prior abstract updates that are
     * overwritten, which does not have to be the case for "maybes".
     *
     * @param update
     *            The abstract update to check.
     * @param assignedBeforeUsed
     *            A set of assigned-before-used operators. Results are added to
     *            the passed set.
     * @param usedBeforeAssigned
     *            A set of used-before-assigned operators. Results are added to
     *            the passed set.
     * @param ec
     *            The {@link ExecutionContext} for handling fields.
     * @param services
     *            The {@link Services} object.
     */
    private static void opsHaveToAssignBeforeUsedForAbstrUpd(final Term update,
            final Set<AbstrUpdateRHS> assignedBeforeUsed,
            final Set<AbstrUpdateRHS> usedBeforeAssigned, ExecutionContext ec,
            Services services) {
        assert update.op() instanceof AbstractUpdate;

        usedBeforeAssigned.addAll(AbstractUpdateFactory.INSTANCE
                .abstractUpdateLocsFromUnionTerm(update.sub(0), ec, services)
                .stream().filter(op -> !assignedBeforeUsed.contains(op))
                .map(AbstrUpdateRHS.class::cast)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>())));

        final AbstractUpdate abstrUpdate = (AbstractUpdate) update.op();
        assignedBeforeUsed.addAll(abstrUpdate.getHasToAssignables().stream()
                .filter(op -> !usedBeforeAssigned.contains(op))
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>())));
    }

    /**
     * Extracts the list of abstract updates from a concatenation of such.
     *
     * @param concatenation
     *            A concatenation of abstract updates
     *            <code>U1 ++ U2 ++ ... ++ Un</code>.
     * @return The contained abstract updates of the concatenation in the
     *         original order.
     */
    public static List<Term> abstractUpdatesFromConcatenation(
            Term concatenation) {
        final List<Term> result = new ArrayList<>();

        if (concatenation.op() instanceof AbstractUpdate) {
            result.add(concatenation);
        } else if (concatenation.op() == UpdateJunctor.CONCATENATED_UPDATE) {
            result.addAll(
                    abstractUpdatesFromConcatenation(concatenation.sub(0)));
            result.addAll(
                    abstractUpdatesFromConcatenation(concatenation.sub(1)));
        } else {
            throw new RuntimeException(
                    "Not an abstract update or concatenation: "
                            + concatenation);
        }

        return result;
    }

    /**
     * Checks whether an {@link AbstractUpdate} accesses the allLocs location
     * set.
     *
     * @param update
     *            The {@link AbstractUpdate} to check.
     * @param services
     *            The {@link Services} object (for the {@link LocSetLDT}).
     * @return true iff the {@link AbstractUpdate} accesseaccesses allLocs
     *         location set.
     */
    public static boolean accessesAllLocs(Term update, Services services) {
        final Operator allLocs = services.getTypeConverter().getLocSetLDT()
                .getAllLocs();
        return getAccessiblesForAbstractUpdate(update,
                services.getTermBuilder()).stream()
                        .anyMatch(t -> t.op() == allLocs);
    }

    public static Term replaceVarInTerm(LocationVariable pv, Term t,
            final Term replaceIn, Services services) {
        final Map<Term, Term> substMap = new HashMap<>();
        substMap.put(services.getTermBuilder().var(pv), t);
        final OpReplacer opRepl = new OpReplacer(substMap,
                services.getTermFactory());
        final Term newAbstrUpdLHS = opRepl.replace(replaceIn);
        return newAbstrUpdLHS;
    }

    public static Set<LocationVariable> collectLocVars(Services services,
            final Term xInst) {
        final OpCollector opColl = new OpCollector();
        xInst.execPostOrder(opColl);
        final Set<LocationVariable> occurringLocVars = opColl.ops().stream()
                .filter(op -> op instanceof LocationVariable)
                .map(LocationVariable.class::cast).collect(Collectors.toSet());

        if (xInst.containsJavaBlockRecursive()) {
            final JavaBlock jb = MergeRuleUtils.getJavaBlockRecursive(xInst);
            final ProgramVariableCollector pvc = new ProgramVariableCollector(
                    jb.program(), services);
            pvc.start();
            occurringLocVars.addAll(pvc.result());
        }
        return occurringLocVars;
    }
}
