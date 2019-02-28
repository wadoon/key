package de.uka.ilkd.key.abstractexecution.util;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.abstractexecution.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.ldt.SetLDT;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.op.UpdateableOperator;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * Utility functions for abtract execution.
 *
 * @author Dominic Steinhoefel
 */
public class AbstractExecutionUtils {
    /**
     * Returns the accessible {@link Term}s of the "right" no-behavior contract
     * for the given {@link AbstractPlaceholderStatement}.
     *
     * @param aps
     *            The {@link AbstractPlaceholderStatement} for which to return
     *            the accessible {@link Term}s.
     * @param context
     *            The context program (for choosing the "right" contract).
     * @param services
     *            The {@link Services} object.
     * @return The accessible {@link Term}s for the given
     *         {@link AbstractPlaceholderStatement}.
     */
    public static Set<Term> getAccessibleTermsForNoBehaviorContract(
            AbstractPlaceholderStatement aps, ProgramElement context,
            Services services) {
        final Term accessibleTerm = AbstractExecutionUtils
                .getAccessibleAndAssignableTermsForNoBehaviorContract(aps,
                        context, services).first;
        return services.getTermBuilder().setUnionToSet(accessibleTerm);
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
                .stream().map(Term::op)
                .filter(ProgramVariable.class::isInstance)
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

        return MiscTools
                .disasembleSetTerm(assignableTerm,
                        services.getTypeConverter().getLocSetLDT().getUnion())
                .stream().map(locSetElemTermsToOpMapper(services))
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
        } else {
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
                pvColl.result(), Optional.empty(), services);
    }

    /**
     * Extracts the accessible and assignable term for the given
     * {@link AbstractPlaceholderStatement} based on the current context from
     * the {@link SpecificationRepository}. The default for both is allLocs
     * (everything assignable and accessible). The returned {@link Term}s are
     * SetLDT unions (not LocSets!). Field accesses are transformed to LocSet
     * singletons for assignable terms and select terms for accessible terms.
     *
     * @param abstrStmt
     *            The {@link AbstractPlaceholderStatement} for which to extract
     *            the accessible and assignable clause.
     * @param surroundingVars
     *            {@link LocationVariable}s in the context to distinguish
     *            several contracts.
     * @param executionContext
     *            An {@link Optional} {@link ExecutionContext} -- make sure to
     *            actually pass one if the generated {@link Term}s should be
     *            used for creating abstract updates. The contained runtime
     *            instance {@link ReferencePrefix} is used to replace "self"
     *            variable occurrences.
     * @param services
     *            The {@link Services} object.
     * @return A pair of (1) the accessible and (2) the assignable clause for
     *         the {@link AbstractPlaceholderStatement}.
     */
    public static Pair<Term, Term> getAccessibleAndAssignableTermsForNoBehaviorContract(
            final AbstractPlaceholderStatement abstrStmt,
            final Set<LocationVariable> surroundingVars,
            Optional<ExecutionContext> executionContext,
            final Services services) {
        final TermBuilder tb = services.getTermBuilder();

        Term accessibleClause;
        Term assignableClause;

        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();

        final List<BlockContract> contracts = //
                getNoBehaviorContracts(abstrStmt, services);

        if (contracts.isEmpty()) {
            accessibleClause = locSetRHSToSetRHS(
                    tb.func(locSetLDT.getAllLocs()), executionContext,
                    services);
            assignableClause = tb.setSingleton(tb.func(locSetLDT.getAllLocs()));
        } else {
            final LocationVariable heap = services.getTypeConverter()
                    .getHeapLDT().getHeap();

            final BlockContract contract = findRightContract(contracts,
                    surroundingVars, heap, services);

            accessibleClause = locSetRHSToSetRHS(
                    contract.getAccessibleClause(heap), executionContext,
                    services);
            assignableClause = locSetLHSToSetLHS(contract.getAssignable(heap),
                    executionContext, services);
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
                surroundingVars,
                Optional.of(
                        matchCond.getInstantiations().getExecutionContext()),
                services);
    }

    /**
     * Converts a union {@link Term} of {@link LocSetLDT} to a corresponding
     * union {@link Term} of {@link SetLDT};
     *
     * @param t
     *            The union {@link Term} to convert.
     * @param services
     *            The {@link Services} project.
     * @return The converted {@link Term}.
     */
    public static Term locSetUnionToSetUnion(Term t, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        return collectElementsOfLocSetTerm(t, locSetLDT.getUnion(), services)
                .stream()
                .map(op -> op instanceof Function ? tb.func((Function) op)
                        : tb.var((ProgramVariable) op))
                .map(tb::setSingleton)
                .reduce(tb.setEmpty(), (t1, t2) -> tb.setUnion(t1, t2));
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
     * Returns all nullary operators in the LHS of the {@link AbstractUpdate}
     * represented by the given update {@link Term}, which also may be a
     * concatenation. In the latter case, the assignables for all contained
     * {@link AbstractUpdate}s are returned.
     *
     * @param update
     *            The abstract update term.
     * @return The assignables of the given (concatenation of)
     *         {@link AbstractUpdate}s.
     */
    public static Set<Operator> getHasToAssignablesForAbstractUpdate(
            Term update) {
        final Set<Operator> result = new LinkedHashSet<>();

        final Operator updateOp = update.op();

        if (updateOp instanceof AbstractUpdate) {
            result.addAll(((AbstractUpdate) updateOp).getHasToAssignables());
        } else {
            // concatenated update
            assert updateOp == UpdateJunctor.CONCATENATED_UPDATE;
            assert update.subs().size() == 2;

            result.addAll(getHasToAssignablesForAbstractUpdate(update.sub(0)));
            result.addAll(getHasToAssignablesForAbstractUpdate(update.sub(1)));
        }

        return result;
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
     * @param services
     *            The {@link Services} object.
     * @return (1) assigned-before-used and (2) used-before-assigned operators.
     *         Sets are ordered. May be an empty optional if there is a
     *         construct not (yet) supported, in this case, the condition should
     *         not be applicable.
     */
    public static Optional<Pair<Set<Operator>, Set<Operator>>> opsAssignedBeforeUsed(
            Term target, Services services) {
        final Set<Operator> assignedBeforeUsed = new LinkedHashSet<>();
        final Set<Operator> usedBeforeAssigned = new LinkedHashSet<>();

        // Skolem location set or location variable
        /* XXX (DS, 2019-02-27): Now we also have fields! */
        if (AbstractExecutionUtils.isProcVarOrSkolemLocSet(target, services)) {
            usedBeforeAssigned.add(target.op());
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
                    final UpdateableOperator lhs = //
                            ((ElementaryUpdate) elem.op()).lhs();
                    final Term rhs = elem.sub(0);

                    if (AbstractExecutionUtils.isProcVarOrSkolemLocSet(rhs,
                            services)) {
                        if (!assignedBeforeUsed.contains(rhs.op())) {
                            usedBeforeAssigned.add(rhs.op());
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
                        usedBeforeAssigned, services);
            }

            // Concatenated abstract update
            else if (update.op() == UpdateJunctor.CONCATENATED_UPDATE) {
                final List<Term> abstractUpdateTerms = //
                        abstractUpdatesFromConcatenation(update);
                for (Term abstrUpdTerm : abstractUpdateTerms) {
                    opsHaveToAssignBeforeUsedForAbstrUpd(abstrUpdTerm,
                            assignedBeforeUsed, usedBeforeAssigned, services);
                }
            }

            // Something else -- ignore for now, exit (completeness relevant)
            else {
                // Probably a nested application
                return Optional.empty();
            }

            final Pair<Set<Operator>, Set<Operator>> subResult = //
                    opsAssignedBeforeUsed(updateTarget, services).orElse(null);

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
                final Pair<Set<Operator>, Set<Operator>> subResult = //
                        opsAssignedBeforeUsed(sub, services).orElse(null);

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
     * @param services
     *            The {@link Services} object.
     */
    private static void opsHaveToAssignBeforeUsedForAbstrUpd(final Term update,
            final Set<Operator> assignedBeforeUsed,
            final Set<Operator> usedBeforeAssigned, Services services) {
        assert update.op() instanceof AbstractUpdate;

        usedBeforeAssigned
                .addAll(MiscTools
                        .disasembleSetTerm(update.sub(0),
                                services.getTypeConverter().getSetLDT()
                                        .getUnion())
                        .stream().map(t -> t.sub(0)).map(Term::op)
                        .filter(op -> !assignedBeforeUsed.contains(op))
                        .collect(Collectors.toSet()));

        final AbstractUpdate abstrUpdate = (AbstractUpdate) update.op();
        assignedBeforeUsed.addAll(abstrUpdate.getHasToAssignables().stream()
                .filter(op -> !usedBeforeAssigned.contains(op))
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>())));
    }

    /**
     * @param term
     *            The {@link Term} to analyze.
     * @param services
     *            The {@link Services} object.
     * @return true iff the given {@link Term} is a Skolem loc set function or a
     *         program variable.
     */
    public static boolean isProcVarOrSkolemLocSet(Term term,
            Services services) {
        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        final Operator op = term.op();
        return term.arity() == 0 && (op instanceof LocationVariable //
                || (op instanceof Function
                        && ((Function) op).sort() == locSetLDT.targetSort()));
    }

    /**
     * Transforms a set of operators to a set union term. Each operator has to
     * be either a {@link LocationVariable} or a {@link Function}.
     *
     * @param ops
     *            The operators for the union term.
     * @param abstrUpd
     *            The {@link AbstractUpdate} from which these operators
     *            originate from. Needed to tell whether the accessibles are
     *            "have-to" or "maybe".
     * @param services
     *            The {@link Services} object.
     * @return A union term consisting of the operators.
     */
    public static Term opsToSetUnion(Set<Operator> ops, AbstractUpdate abstrUpd,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final List<Term> wrappedOps = new ArrayList<>();
        for (final Operator op : ops) {
            Term t = op instanceof Function ? tb.func((Function) op)
                    : tb.var((LocationVariable) op);

            if (abstrUpd.getHasToAssignables().contains(op)) {
                t = tb.hasTo(t);
            }

            wrappedOps.add(tb.setSingleton(t));
        }

        return tb.setUnion(wrappedOps);
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
     * Checks whether an {@link AbstractUpdate} may assigns the allLocs location
     * set.
     *
     * @param update
     *            The {@link AbstractUpdate} to check.
     * @param services
     *            The {@link Services} object (for the {@link LocSetLDT}).
     * @return true iff the {@link AbstractUpdate} assigns the allLocs location
     *         set.
     */
    public static boolean mayAssignAllLocs(AbstractUpdate update,
            Services services) {
        final Operator allLocs = //
                services.getTypeConverter().getLocSetLDT().getAllLocs();
        return update.getMaybeAssignables().stream()
                .anyMatch(op -> op == allLocs);
    }

    /**
     * Checks whether an {@link AbstractUpdate} may assigns the allLocs location
     * set.
     *
     * @param update
     *            The {@link AbstractUpdate} to check.
     * @param services
     *            The {@link Services} object (for the {@link LocSetLDT}).
     * @return true iff the {@link AbstractUpdate} assigns the allLocs location
     *         set.
     */
    public static boolean hasToAssignAllLocs(AbstractUpdate update,
            Services services) {
        final Operator allLocs = //
                services.getTypeConverter().getLocSetLDT().getAllLocs();
        return update.getHasToAssignables().stream()
                .anyMatch(op -> op == allLocs);
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

    /**
     * Returns the target operators in a set-like union term. Expects a union
     * term consisting of (1) Skolem loc set functions (result will contain that
     * function), (2) singletonPV(...) applications on location variables
     * (result will contain the variable), and (3) singleton(...) applications
     * on an object and a function symbol representing a field (result will
     * contain the function symbol).
     *
     * @param t
     *            The loc set union term to dissect.
     * @param t
     *            The union function symbol, for instance of the LocSet theory.
     * @param services
     *            The {@link Services} object (for {@link TypeConverter}.
     * @return The {@link Operator}s in the {@link Term} (location variables,
     *         field function symbols, and Skolem location set functions).
     */
    public static Set<Operator> collectElementsOfLocSetTerm(Term t,
            Function union, Services services) {
        return MiscTools.disasembleSetTerm(t, union).stream()
                .map(locSetElemTermsToOpMapper(services))
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
    }

    /**
     * A mapper that can be applied to the elements of a loc set union to
     * extract the relevant operator.
     *
     * @param services
     *            The {@link Services} object.
     *
     * @return A mapper to apply on the element {@link Term}s of a loc set
     *         union.
     * @see #locSetElemTermsToOp(Term, Services)
     */
    public static java.util.function.Function<? super Term, ? extends Operator> locSetElemTermsToOpMapper(
            Services services) {
        return elemTerm -> locSetElemTermsToOp(elemTerm, services);
    }

    /**
     * Transforms a loc set union {@link Term} to a set union {@link Term}. The
     * set singleton elements contain program variables, functions, or those two
     * wrapped in hasTo applications.
     *
     * @param elemTerm
     *            The loc set union {@link Term} to convert.
     * @param executionContext
     *            An {@link Optional} {@link ExecutionContext} -- make sure to
     *            actually pass one if the generated {@link Term}s should be
     *            used for creating abstract updates. The contained runtime
     *            instance {@link ReferencePrefix} is used to replace "self"
     *            variable occurrences.
     * @param services
     *            The {@link Services} object.
     * @return A set term corresponding to the loc set {@link Term}.
     */
    public static Term locSetLHSToSetLHS(Term elemTerm,
            Optional<ExecutionContext> executionContext, Services services) {
        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        final TermBuilder tb = services.getTermBuilder();

        final Operator op = elemTerm.op();
        if (op instanceof ProgramVariable) {
            return tb.setSingleton(elemTerm);
        } else if (op instanceof Function && op.arity() == 0) {
            return tb.setSingleton(elemTerm);
        } else if (op == locSetLDT.getSingletonPV()) {
            return locSetLHSToSetLHS(elemTerm.sub(0), executionContext,
                    services);
        } else if (op == locSetLDT.getSingleton()) {
            /*
             * TODO (DS, 2019-02-27): Only replace "self" by runtime instance!
             */
            return executionContext.map(ExecutionContext::getRuntimeInstance)
                    .map(LocationVariable.class::cast)
                    .map(obj -> tb.setSingleton(
                            tb.singleton(tb.var(obj), elemTerm.sub(1))))
                    .orElse(locSetLHSToSetLHS(elemTerm.sub(1), executionContext,
                            services));
        } else if (op == locSetLDT.getHasTo()) {
            return tb.setSingleton(tb.hasTo(locSetLHSToSetLHS(elemTerm.sub(0),
                    executionContext, services).sub(0)));
        } else if (op == locSetLDT.getUnion()) {
            return tb.setUnion(
                    locSetLHSToSetLHS(elemTerm.sub(0), executionContext,
                            services),
                    locSetLHSToSetLHS(elemTerm.sub(1), executionContext,
                            services));
        } else if (services.getTypeConverter().getHeapLDT().isSelectOp(op)) {
            /*
             * TODO (DS, 2019-02-27): Only replace "self" by runtime instance!
             */
            return executionContext.map(ExecutionContext::getRuntimeInstance)
                    .map(LocationVariable.class::cast)
                    .map(obj -> tb.setSingleton(
                            tb.singleton(tb.var(obj), elemTerm.sub(2))))
                    .orElse(locSetLHSToSetLHS(elemTerm.sub(2), executionContext,
                            services));
        } else {
            assert false : "Unexpected element of loc set union.";
            return null;
        }
    }

    /**
     * Transforms a LocSet union {@link Term} (right-hand side of an
     * {@link AbstractPlaceholderStatement} specification) to a set union
     * {@link Term} as is expected by an {@link AbstractUpdate}. hasTo
     * applications are removed, and singleton(o,f) applications are transformed
     * to select applications, such that the heap can be applied on the
     * {@link AbstractUpdate} right-hand side.
     *
     * @param elemTerm
     *            The element of the (loc) set union.
     * @param executionContext
     *            An {@link Optional} {@link ExecutionContext} -- make sure to
     *            actually pass one if the generated {@link Term}s should be
     *            used for creating abstract updates. The contained runtime
     *            instance {@link ReferencePrefix} is used to replace "self"
     *            variable occurrences.
     * @param services
     *            The {@link Services} object.
     * @return The relevant {@link Operator} of the (loc) set union.
     */
    public static Term locSetRHSToSetRHS(Term elemTerm,
            Optional<ExecutionContext> executionContext, Services services) {
        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        final TermBuilder tb = services.getTermBuilder();

        final Operator op = elemTerm.op();
        if (op instanceof ProgramVariable) {
            return tb.setSingleton(elemTerm);
        } else if (op instanceof Function && op.arity() == 0) {
            return tb.setSingleton(elemTerm);
        } else if (op == locSetLDT.getSingletonPV()) {
            return locSetRHSToSetRHS(elemTerm.sub(0), executionContext,
                    services);
        } else if (op == locSetLDT.getSingleton()) {
            // TODO (DS, 2019-02-27): Only replace "self" by runtime instance!
            return executionContext.map(ExecutionContext::getRuntimeInstance)
                    .map(LocationVariable.class::cast)
                    .map(obj -> tb.setSingleton(tb.dot(elemTerm.sub(1).sort(),
                            tb.var(obj), elemTerm.sub(1))))
                    .orElse(locSetRHSToSetRHS(elemTerm.sub(1), executionContext,
                            services));
        } else if (op == locSetLDT.getHasTo()) {
            return locSetRHSToSetRHS(elemTerm.sub(0), executionContext,
                    services);
        } else if (op == locSetLDT.getUnion()) {
            return tb.setUnion(
                    locSetRHSToSetRHS(elemTerm.sub(0), executionContext,
                            services),
                    locSetRHSToSetRHS(elemTerm.sub(1), executionContext,
                            services));
        } else {
            assert false : "Unexpected element of (loc) set union.";
            return null;
        }
    }

    /**
     * Extracts the relevant operator for an element of a set / loc set union.
     * E.g., for a singleton(self, someField) returns someField.
     *
     * @param elemTerm
     *            The element of the (loc) set union.
     * @param services
     *            The {@link Services} object.
     * @return The relevant {@link Operator} of the (loc) set union.
     */
    public static Operator locSetElemTermsToOp(Term elemTerm,
            Services services) {
        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        final SetLDT setLDT = services.getTypeConverter().getSetLDT();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();

        final Operator op = elemTerm.op();
        if (op instanceof ProgramVariable) {
            return op;
        } else if (op instanceof Function && op.arity() == 0) {
            return elemTerm.op();
        } else if (op == locSetLDT.getSingletonPV()) {
            return locSetElemTermsToOp(elemTerm.sub(0), services);
        } else if (op == locSetLDT.getSingleton()) {
            return locSetElemTermsToOp(elemTerm.sub(1), services);
        } else if (op == setLDT.getSingleton()) {
            return locSetElemTermsToOp(elemTerm.sub(0), services);
        } else if (op == locSetLDT.getHasTo()) {
            return locSetElemTermsToOp(elemTerm.sub(0), services);
        } else if (heapLDT.isSelectOp(op)) {
            return locSetElemTermsToOp(elemTerm.sub(2), services);
        } else {
            assert false : "Unexpected element of (loc) set union.";
            return null;
        }
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
