// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.util;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.UniqueArrayList;

import de.uka.ilkd.key.abstractexecution.java.AbstractProgramElement;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.HasToLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * Utility methods for finding abstract execution contracts and retrieving
 * information from them.
 *
 * @author Dominic Steinhoefel
 */
public class AbstractExecutionContractUtils {

    /**
     * Returns the accessible locations of the "right" no-behavior contract for the
     * given {@link AbstractProgramElement}.
     *
     * @param aps           The {@link AbstractProgramElement} for which to return
     *                      the accessible locations.
     * @param context       The context program (for choosing the "right" contract).
     * @param localSpecRepo TODO
     * @param services      The {@link Services} object.
     * @return The accessible locations for the given
     *         {@link AbstractProgramElement}.
     */
    public static List<Term> getAccessibleTermsForNoBehaviorContract(AbstractProgramElement aps,
            ProgramElement context, GoalLocalSpecificationRepository localSpecRepo,
            Services services) {
        return getAccessibleAndAssignableTermsForNoBehaviorContract(aps, context, localSpecRepo,
                services).getAccesibles();
    }

    /**
     * Returns the accessible {@ProgramVariable}s of the "right" no-behavior
     * contract for the given {@link AbstractProgramElement}.
     *
     * @param aps           The {@link AbstractProgramElement} for which to return
     *                      the accessible {@link ProgramVariable}s.
     * @param context       The context program (for choosing the "right" contract).
     * @param localSpecRepo TODO
     * @param services      The {@link Services} object.
     * @return The accessible {@link ProgramVariable}s for the given
     *         {@link AbstractProgramElement}.
     */
    public static List<ProgramVariable> getAccessibleProgVarsForNoBehaviorContract(
            AbstractProgramElement aps, ProgramElement context,
            GoalLocalSpecificationRepository localSpecRepo, Services services) {
        return getAccessibleTermsForNoBehaviorContract(aps, context, localSpecRepo, services)
                .stream().filter(PVLoc.class::isInstance).map(PVLoc.class::cast).map(PVLoc::getVar)
                .map(ProgramVariable.class::cast).collect(Collectors.toList());
    }

    /**
     * Returns the assignable locations of the "right" no-behavior contract for the
     * given {@link AbstractProgramElement}.
     *
     * @param aps           The {@link AbstractProgramElement} for which to return
     *                      the assignable locations.
     * @param context       The context program (for choosing the "right" contract).
     * @param localSpecRepo TODO
     * @param services      The {@link Services} object.
     * @return The assignable locations for the given
     *         {@link AbstractProgramElement}.
     */
    public static UniqueArrayList<AbstractUpdateLoc> getAssignableOpsForNoBehaviorContract(
            AbstractProgramElement aps, ProgramElement context,
            GoalLocalSpecificationRepository localSpecRepo, Services services) {
        return getAccessibleAndAssignableTermsForNoBehaviorContract(aps, context, localSpecRepo,
                services).getAssignables();
    }

    /**
     * Returns the assignable {@ProgramVariable}s of the "right" no-behavior
     * contract for the given {@link AbstractProgramElement}.
     *
     * @param aps           The {@link AbstractProgramElement} for which to return
     *                      the assignable {@link ProgramVariable}s.
     * @param context       The context program (for choosing the "right" contract).
     * @param localSpecRepo TODO
     * @param services      The {@link Services} object.
     * @return The assignable {@link ProgramVariable}s for the given
     *         {@link AbstractProgramElement}.
     */
    public static List<ProgramVariable> getAssignableProgVarsForNoBehaviorContract(
            AbstractProgramElement aps, ProgramElement context,
            GoalLocalSpecificationRepository localSpecRepo, Services services) {
        return getAssignableOpsForNoBehaviorContract(aps, context, localSpecRepo, services).stream()
                .map(loc -> loc instanceof HasToLoc ? ((HasToLoc<?>) loc).child() : loc)
                .filter(PVLoc.class::isInstance).map(PVLoc.class::cast).map(PVLoc::getVar)
                .map(LocationVariable.class::cast).collect(Collectors.toList());
    }

    /**
     * Selects, amongst a given list of {@link BlockContract}s, the matching one for
     * the current context. Note that the current implementation is quite ad-hoc
     * (see inlined TODO in
     * {@link #findRightContract(List, ProgramElement, LocationVariable, GoalLocalSpecificationRepository, Services)}).
     *
     * @param contracts     The list of contracts for the placeholder statement.
     * @param svInst        The {@link SVInstantiations}.
     * @param heap          The heap term.
     * @param localSpecRepo TODO
     * @param services      The services object.
     * @return The most suitable {@link BlockContract} of the list. Will return null
     *         iff the given contracts list is empty.
     */
    public static BlockContract findRightContract(final List<BlockContract> contracts,
            final SVInstantiations svInst, final LocationVariable heap,
            GoalLocalSpecificationRepository localSpecRepo, Services services) {
        return findRightContract(contracts, svInst.getContextInstantiation().contextProgram(), heap,
                localSpecRepo, services);
    }

    /**
     * Selects, amongst a given list of {@link BlockContract}s, the matching one for
     * the current program context. Note that the current implementation is quite
     * ad-hoc.
     *
     * @param contracts      The list of contracts for the placeholder statement.
     * @param contextProgram The context program (for choosing the right contract).
     * @param heap           The heap term.
     * @param localSpecRepo  TODO
     * @param services       The services object.
     * @return The most suitable {@link BlockContract} of the list. Will return null
     *         iff the given contracts list is empty.
     */
    public static BlockContract findRightContract(final List<BlockContract> contracts,
            final ProgramElement contextProgram, final LocationVariable heap,
            GoalLocalSpecificationRepository localSpecRepo, Services services) {
        final ProgramVariableCollector pvColl = //
                new ProgramVariableCollector(contextProgram, localSpecRepo, services);
        pvColl.start();
        return findRightContract(contracts, pvColl.result(), heap, localSpecRepo, services);
    }

    /**
     * Selects, amongst a given list of {@link BlockContract}s, the matching one for
     * the current context. Note that the current implementation is quite ad-hoc
     * (see inlined TODO). The principle is that the contract with most variables in
     * common (that is actually, the least number of variables NOT in common) with
     * the given set of context variables <code>surroundingVars</code> will be
     * selected. In case of a draw, the first one wins.
     *
     * @param contracts      The list of contracts for the placeholder statement.
     * @param heap           The heap term.
     * @param localSpecRepo  TODO
     * @param services       The services object.
     * @param contextProgram The context program (for choosing the right contract).
     * @return The most suitable {@link BlockContract} of the list. Will return null
     *         iff the given contracts list is empty.
     */
    public static BlockContract findRightContract(final List<BlockContract> contracts,
            final Set<LocationVariable> surroundingVars, final LocationVariable heap,
            GoalLocalSpecificationRepository localSpecRepo, Services services) {
        assert contracts != null && !contracts.isEmpty();

        /*
         * TODO (DS, 2018-12-21): Choose the right contract! There is probably a
         * contract from the other branch with wrong renamings. We somehow have to find
         * the right one. Ideas: (1) Get all PVs from context and choose the contract
         * with most PVs in common, or (2) store a node ID for the contract in
         * ProgVarReplacer when replacing, such that we can get the contract assigned to
         * a node which is an ancestor of this one, or (3) check the Goal-local
         * namespaces such that we choose the contract for which the locals are known.
         * We could also make the contracts goal-local somehow. Option (1) is the
         * ugliest which also might fail, but the other ones require more actions or
         * passing through more parameters to this method.
         *
         * Below, there is a quick implementation of method (1).
         */

        /*
         * Sort such that a contract with more variables in common comes first, and if
         * two contracts have the same number of variables in common, than the newer
         * contract comes first.
         */
        contracts.sort(new Comparator<BlockContract>() {
            @Override
            public int compare(BlockContract c1, BlockContract c2) {
                final int sharedVarsDiff = numSharedVars(surroundingVars, c2, localSpecRepo,
                        services) - numSharedVars(surroundingVars, c1, localSpecRepo, services);
                // c1 is smaller if sharing *more* variables
                if (sharedVarsDiff < 0) {
                    return -1;
                } else if (sharedVarsDiff > 0) {
                    return 1;
                }

                assert sharedVarsDiff == 0;

                final int varsNotSharedDiff = numOfVarsNotInCcommon(surroundingVars, c1,
                        localSpecRepo, services)
                        - numOfVarsNotInCcommon(surroundingVars, c2, localSpecRepo, services);
                // c1 is smaller if it has a lower number of variables not in common
                if (varsNotSharedDiff < 0) {
                    return -1;
                } else if (varsNotSharedDiff > 0) {
                    return 1;
                }

                assert varsNotSharedDiff == 0;

                // c1 is smaller if newer
                return Math.round(Math.signum(c2.creationTime() - c1.creationTime()));
            }

        });

        return contracts.get(0);
    }

    /**
     * Calculates the number of variables shared by the given contract with the
     * given set of variables.
     * 
     * @param varsToCheck   The variables to check.
     * @param contract      The contract.
     * @param localSpecRepo TODO
     * @param services      The {@link Services} object (for the variable
     *                      collector).
     * @return The number of shared variables.
     */
    private static int numSharedVars(final Set<LocationVariable> varsToCheck,
            BlockContract contract, GoalLocalSpecificationRepository localSpecRepo,
            Services services) {
        final ProgramVariableCollector pvColl = //
                new ProgramVariableCollector(contract.getBlock(), localSpecRepo, services);
        pvColl.performActionOnBlockContract(contract);
        return (int) pvColl.result().stream().filter(varsToCheck::contains).count();
    }

    /**
     * Calculates the number of variables which the given contract has not in common
     * with the given set of variables.
     * 
     * @param varsToCheck   The variables to check.
     * @param contract      The contract.
     * @param localSpecRepo TODO
     * @param services      The {@link Services} object (for the variable
     *                      collector).
     * @return The number of shared variables.
     */
    private static int numOfVarsNotInCcommon(final Set<LocationVariable> varsToCheck,
            BlockContract contract, GoalLocalSpecificationRepository localSpecRepo,
            Services services) {
        final ProgramVariableCollector pvColl = //
                new ProgramVariableCollector(contract.getBlock(), localSpecRepo, services);
        pvColl.performActionOnBlockContract(contract);
        return (int) pvColl.result().stream().filter(pv -> !varsToCheck.contains(pv)).count()
                + (int) varsToCheck.stream().filter(pv -> !pvColl.result().contains(pv)).count();
    }

    /**
     * Extracts the accessible and assignable locations for the given
     * {@link AbstractProgramElement} based on the current context from the
     * {@link SpecificationRepository}. The default for both is allLocs (everything
     * assignable and accessible).
     *
     * @param abstrStmt      The {@link AbstractProgramElement} for which to extract
     *                       the accessible and assignable clause.
     * @param contextProgram The context program to determine the right contract
     *                       (after renamings).
     * @param localSpecRepo  TODO
     * @param services       The {@link Services} object.
     * @return A pair of (1) the accessible and (2) the assignable locations for the
     *         {@link AbstractProgramElement}.
     */
    public static AEFrameSpecs getAccessibleAndAssignableTermsForNoBehaviorContract(
            final AbstractProgramElement abstrStmt, final ProgramElement contextProgram,
            GoalLocalSpecificationRepository localSpecRepo, final Services services) {
        final ProgramVariableCollector pvColl = //
                new ProgramVariableCollector(contextProgram, localSpecRepo, services);
        pvColl.start();

        final Function dummy = new Function(new Name(services.getTermBuilder().newName("_DUMMY")),
                Sort.FORMULA, pvColl.result().stream().map(LocationVariable::sort)
                        .collect(ImmutableArray.toImmutableArray()));
        final TermBuilder tb = services.getTermBuilder();

        return getAccessibleAndAssignableLocsForNoBehaviorContract(abstrStmt,
                Optional.of(new SequentFormula(tb.func(dummy,
                        pvColl.result().stream().map(tb::var).toArray(Term[]::new)))),
                Optional.empty(), localSpecRepo, services);
    }

    /**
     * Extracts the accessible and assignable locations for the given
     * {@link AbstractProgramElement} based on the current context from the
     * {@link SpecificationRepository}. The default for both is allLocs (everything
     * assignable and accessible).
     *
     * @param abstrStmt       The {@link AbstractProgramElement} for which to
     *                        extract the accessible and assignable clause.
     * @param localSpecRepo   TODO
     * @param services        The {@link Services} object.
     * @param surroundingVars {@link LocationVariable}s in the context to
     *                        distinguish several contracts.
     * @return A pair of (1) the accessible terms and (2) the assignable locations
     *         for the {@link AbstractProgramElement}.
     */
    public static AEFrameSpecsInterm getAccessibleAndAssignableTermsForNoBehaviorContract(
            final AbstractProgramElement abstrStmt, final Optional<SequentFormula> maybeSeqFor,
            GoalLocalSpecificationRepository localSpecRepo, final Services services) {
        final List<BlockContract> contracts = //
                getNoBehaviorContracts(abstrStmt, localSpecRepo, services);

        if (contracts.isEmpty()) {
            return new AEFrameSpecsInterm(services.getTermBuilder().allLocs(),
                    services.getTermBuilder().allLocs());
        } else {
            final LocationVariable heap = services.getTypeConverter().getHeapLDT().getHeap();
            final BlockContract contract = //
                    findRightContract(contracts, collectSurroundingVars(maybeSeqFor), heap,
                            localSpecRepo, services);

            return new AEFrameSpecsInterm(contract.getAssignable(heap),
                    contract.getAccessibleClause(heap), contract.getInfFlowSpecs());
        }
    }

    /**
     * Extracts the accessible and assignable locations for the given
     * {@link AbstractProgramElement} based on the current context from the
     * {@link SpecificationRepository}. The default for both is allLocs (everything
     * assignable and accessible).
     *
     * @param abstrStmt        The {@link AbstractProgramElement} for which to
     *                         extract the accessible and assignable clause.
     * @param surroundingVars  {@link LocationVariable}s in the context to
     *                         distinguish several contracts.
     * @param executionContext An optional runtime instance {@link LocationVariable}
     *                         to normalize self terms (because otherwise, there
     *                         might be different such terms around).
     * @param localSpecRepo    TODO
     * @param services         The {@link Services} object.
     * @return A pair of (1) the accessible terms and (2) the assignable locations
     *         for the {@link AbstractProgramElement}.
     */
    public static AEFrameSpecs getAccessibleAndAssignableLocsForNoBehaviorContract(
            final AbstractProgramElement abstrStmt, final Optional<SequentFormula> maybeSeqFor,
            Optional<ExecutionContext> executionContext,
            GoalLocalSpecificationRepository localSpecRepo, final Services services) {
        final AEFrameSpecsInterm termResult = getAccessibleAndAssignableTermsForNoBehaviorContract(
                abstrStmt, maybeSeqFor, localSpecRepo, services);
        return new AEFrameSpecs(termResult, executionContext, services);
    }

    /**
     * If maybeSeqFor is present, returns the surrounding variables found in the
     * formula. Otherwise, the empty set.
     * 
     * @param maybeSeqFor The formula from which to obtain the variables.
     * @return The set of variables.
     */
    public static Set<LocationVariable> collectSurroundingVars(
            final Optional<SequentFormula> maybeSeqFor) {
        final Set<LocationVariable> surroundingVars = new LinkedHashSet<>();
        /*
         * NOTE (DS, 2019-11-04): Considering the program proved to be a bad idea, since
         * then, all block contracts (also the "wrong" ones) of APSs will be considered,
         * leading to a wrong result. The sequent is more reliable.
         */
//        final ProgramVariableCollector pvc = //
//                new ProgramVariableCollector(
//                        matchCond.getInstantiations().getContextInstantiation().contextProgram(),
//                        services);
//        pvc.start();
//        surroundingVars.addAll(pvc.result());
        maybeSeqFor.ifPresent(sf -> {
            /*
             * NOTE (DS, 2019-01-30): Here, we just could use a TermProgramVariableCollector
             * and thus also consider PVs in the programs. However, those might arise from
             * one of the multiple contracts with differently named versions. In those
             * cases, we prefer, in case of name collisions, those PVs that occur in terms.
             */
            final OpCollector opColl = new OpCollector();
            sf.formula().execPostOrder(opColl);
            final Set<LocationVariable> result = opColl.ops().stream()
                    .filter(LocationVariable.class::isInstance).map(LocationVariable.class::cast)
                    .collect(Collectors.toSet());
//            surroundingVars.removeIf(
//                    lv1 -> result.stream().anyMatch(lv2 -> lv1.toString().equals(lv2.toString())));
            surroundingVars.addAll(result);
        });
        return surroundingVars;
    }

    /**
     * Returns the contracts for the given {@link AbstractProgramElement}. This
     * refers to the "standard" contracts, i.e. without any specific behavior (like
     * "exceptional_behavior" etc.).
     *
     * @param abstrStmt     The {@link AbstractProgramElement} for which to return
     *                      the contracts.
     * @param localSpecRepo TODO
     * @param services      The {@link Services} object.
     * @return All the contracts for the given {@link AbstractProgramElement}.
     */
    public static List<BlockContract> getNoBehaviorContracts(final AbstractProgramElement abstrStmt,
            GoalLocalSpecificationRepository localSpecRepo, final Services services) {
        return localSpecRepo.getAbstractProgramElementContracts(abstrStmt).stream()
                .filter(contract -> contract.getBaseName().equals("JML block contract"))
                /*
                 * We exclude return_behavior etc. here, because from those contracts we only
                 * consider the precondition.
                 */
                .collect(Collectors.toList());
    }

    public static class AEFrameSpecs {
        private final UniqueArrayList<AbstractUpdateLoc> assignables;
        private final List<Term> accesibles;
        private final Map<List<AbstractUpdateLoc>, List<Term>> determines;

        public AEFrameSpecs(AEFrameSpecsInterm intermSpecs, Optional<ExecutionContext> ec,
                final Services services) {
            final UniqueArrayList<AbstractUpdateLoc> assignablesList = processAssignables(
                    intermSpecs, ec, services);
            final List<Term> accessiblesList = processAccessibles(intermSpecs, ec, services);
            final Map<List<AbstractUpdateLoc>, List<Term>> determines = processIFSpecs(
                    intermSpecs.getDetermines(), assignablesList, accessiblesList, ec, services);

            this.assignables = assignablesList;
            this.accesibles = accessiblesList;
            this.determines = determines;
        }

        public List<Term> getAccesibles() {
            return accesibles;
        }

        public UniqueArrayList<AbstractUpdateLoc> getAssignables() {
            return assignables;
        }

        public Map<List<AbstractUpdateLoc>, List<Term>> getDetermines() {
            return determines;
        }

        private static UniqueArrayList<AbstractUpdateLoc> processAssignables(
                AEFrameSpecsInterm intermSpecs, Optional<ExecutionContext> ec,
                final Services services) {
            return services.getTermBuilder().locsetUnionToSet(intermSpecs.getAssignables()).stream()
                    .map(t -> AbstractUpdateFactory.abstrUpdateLocFromTerm(t, ec, services))
                    .collect(Collectors.toCollection(() -> new UniqueArrayList<>()));
        }

        private static List<Term> processAccessibles(AEFrameSpecsInterm intermSpecs,
                Optional<ExecutionContext> ec, final Services services) {
            final List<Term> accessibleClause = services.getTermBuilder()
                    .locsetUnionToSet(intermSpecs.getAccesibles()).stream()
                    .collect(Collectors.toList());

            List<Term> accessiblesList = accessibleClause;
            if (ec.isPresent()) {
                accessiblesList = accessibleClause.stream().map(
                        term -> AbstractUpdateFactory.normalizeSelfVarInTerm(term, ec, services))
                        .collect(Collectors.toList());
            }

            return accessiblesList;
        }

        private static Map<List<AbstractUpdateLoc>, List<Term>> processIFSpecs(
                ImmutableList<InfFlowSpec> infFlowSpecs,
                UniqueArrayList<AbstractUpdateLoc> assignables, List<Term> accesibles,
                Optional<ExecutionContext> ec, final Services services)
                throws IllegalArgumentException {
            final Map<List<AbstractUpdateLoc>, List<Term>> result = new LinkedHashMap<>();

            for (final InfFlowSpec ifspec : infFlowSpecs) {
                final List<AbstractUpdateLoc> detlist = new ArrayList<>();
                final List<Term> bylist = new ArrayList<>();

                for (final AbstractUpdateLoc detloc : ifspec.postExpressions.stream()
                        .map(t -> AbstractUpdateFactory.abstrUpdateLocFromTerm(t, ec, services))
                        .collect(Collectors.toList())) {
                    if (!assignables.contains(detloc)) {
                        throw new IllegalArgumentException(String.format(
                                "Location %s of determines clause not contained in assignables list",
                                detloc));
                    }

                    detlist.add(detloc);
                }

                for (final Term byloc : ifspec.preExpressions) {
                    if (!accesibles.contains(byloc)) {
                        throw new IllegalArgumentException(String.format(
                                "Location %s of determines (\\by) clause not contained in assignables list",
                                byloc));
                    }

                    bylist.add(byloc);
                }

                // Assert that determined locations are disjoint
                for (final List<AbstractUpdateLoc> previousDetLocs : result.keySet()) {
                    if (!Collections.disjoint(previousDetLocs, detlist)) {
                        throw new IllegalArgumentException(String.format(
                                "Locations on right-hand side of \\by specification "
                                        + "in determines clause have to be disjoint in AE, given: %s and %s",
                                previousDetLocs.toString(), detlist.toString()));
                    }
                }
            }

            return result;
        }
    }

    public static class AEFrameSpecsInterm {
        private final Term assignables;
        private final Term accesibles;
        private final ImmutableList<InfFlowSpec> determines;

        public AEFrameSpecsInterm(Term assignables, Term accesibles) {
            this.assignables = assignables;
            this.accesibles = accesibles;
            this.determines = ImmutableSLList.<InfFlowSpec>nil();
        }

        public AEFrameSpecsInterm(Term assignables, Term accesibles,
                ImmutableList<InfFlowSpec> determines) {
            this.assignables = assignables;
            this.accesibles = accesibles;
            this.determines = determines;
        }

        public Term getAssignables() {
            return assignables;
        }

        public Term getAccesibles() {
            return accesibles;
        }

        public ImmutableList<InfFlowSpec> getDetermines() {
            return determines;
        }
    }

}