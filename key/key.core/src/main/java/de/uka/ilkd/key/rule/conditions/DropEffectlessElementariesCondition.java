// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.conditions;

import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uka.ilkd.key.abstractexecution.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.SkolemLoc;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionContractUtils;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

public final class DropEffectlessElementariesCondition implements VariableCondition {
    private final UpdateSV uSV;
    private final SchemaVariable targetSV;
    private final SchemaVariable resultSV;

    public DropEffectlessElementariesCondition(UpdateSV uSV, SchemaVariable targetSV,
            SchemaVariable resultSV) {
        this.uSV = uSV;
        this.targetSV = targetSV;
        this.resultSV = resultSV;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate, MatchConditions mc,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final SVInstantiations svInst = mc.getInstantiations();

        final Term update = (Term) svInst.getInstantiation(uSV);
        final Term target = (Term) svInst.getInstantiation(targetSV);
        final Term previousResult = (Term) svInst.getInstantiation(resultSV);

        if (update == null || target == null) {
            return mc;
        }

        final Optional<Term> maybeResult = //
                dropEffectlessElementaries( //
                        update, //
                        target, //
                        collectLocations(target, services), //
                        services).map( //
                                upd -> tb.apply(upd, target, null));

        if (!maybeResult.isPresent()) {
            return null;
        }

        final Term result = maybeResult.get();
        if (previousResult == null) {
            return mc.setInstantiations(svInst.add(resultSV, result, services));
        } else if (previousResult.equals(result)) {
            return mc;
        } else {
            return null;
        }
    }

    /**
     * Collects read locations in the target {@link Term}.
     * 
     * @param target   The {@link Term} from which to collect locations.
     * @param services The {@link Services} object.
     * @return The relevant locations in {@link Term}.
     */
    private static Set<LocationVariable> collectLocations(Term target, Services services) {
        final TermProgramVariableCollector collector = services.getFactory().create(services);
        target.execPostOrder(collector);
        final Set<LocationVariable> varsInTarget = collector.result();
        return varsInTarget;
    }

    /**
     * Returns, if possible, a simplified term <code>{update'}target</code> which is
     * equivalent to <code>{update}target</code>. Uses the locations in relevantVars
     * to decide what to drop in the simplification step (updates not assigning
     * relevant variables can be dropped). Returns {@link Optional#empty()} if
     * simplification is not possible.
     * 
     * @param update   The update to simplify.
     * @param target   The target formula, for extracting locations.
     * @param services The {@link Services} object.
     * @return The simplified update application {@link Term}, or
     *         {@link Optional#empty()}.
     */
    private static Optional<Term> dropEffectlessElementaries(final Term update, final Term target,
            final Set<LocationVariable> relevantVars, final Services services) {
        final TermBuilder tb = services.getTermBuilder();

        if (update.op() instanceof ElementaryUpdate) {
            return maybeDropElementaryUpdate(update, target, relevantVars, services);
        } else if (update.op() instanceof AbstractUpdate) {
            return maybeDropOrSimplifyAbstractUpdate(update, target, relevantVars, services);
        } else if (update.op() == UpdateJunctor.PARALLEL_UPDATE) {
            final Term sub1 = update.sub(0);
            final Term sub2 = update.sub(1);

            /*
             * First descend to the second sub-update to keep relevantVars in good order.
             */
            final Optional<Term> maybeNewSub1 = //
                    dropEffectlessElementaries(sub2, target, relevantVars, services);
            final Optional<Term> maybeNewSub0 = //
                    dropEffectlessElementaries(sub1, target, relevantVars, services);

            if (!maybeNewSub0.isPresent() && !maybeNewSub1.isPresent()) {
                return Optional.empty();
            }

            return Optional.of( //
                    tb.parallel(maybeNewSub0.orElse(sub1), maybeNewSub1.orElse(sub2)));
        } else if (update.op() == UpdateApplication.UPDATE_APPLICATION) {
            final Term appliedUpdate = update.sub(0);
            final Term targetUpdate = update.sub(1);

            return dropEffectlessElementaries(targetUpdate, target, relevantVars, services)
                    .map(newSub -> tb.apply(appliedUpdate, newSub, null));
        } else {
            // Unknown operator.
            return Optional.empty();
        }
    }

    /**
     * Returns a SKIP update, a simplified abstract update (less assignables), or an
     * empty optional if no simplification is possible. Like
     * {@link #dropElementary(Term, Term, Set, Services, TermBuilder)}, but for the
     * much more complex setting of an abstract update.
     * 
     * @param update   The abstract update to check.
     * @param target   The target formula, for extracting locations.
     * @param services The {@link Services} object.
     * @return The simplified update {@link Term}, or {@link Optional#empty()}.
     */
    private static Optional<Term> maybeDropOrSimplifyAbstractUpdate(final Term update,
            final Term target, final Set<LocationVariable> relevantVars, final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final AbstractUpdate abstrUpd = (AbstractUpdate) update.op();

        final Predicate<LocationVariable> hasToAssign = //
                rv -> abstrUpd.hasToAssign((AbstractUpdateLoc) new PVLoc(rv));
        final Predicate<LocationVariable> mayAssign = //
                rv -> abstrUpd.mayAssign((AbstractUpdateLoc) new PVLoc(rv));

        if (relevantVars.stream().anyMatch(hasToAssign)) {
            relevantVars.removeIf(hasToAssign);
            return Optional.empty();
        } else if (!relevantVars.stream().anyMatch(mayAssign)) {
            /*
             * We're looking for a PV which doesn't exist, which effectively means that
             * we're looking for the allLocs symbol in accessibles of APSs, since then, we
             * can only drop the APS if it does not assign anything.
             */
            final LocationVariable nonexistingPV = new LocationVariable(
                    new ProgramElementName("XXX-XXX"),
                    services.getTypeConverter().getBooleanType());

            /*
             * XXX (DS, 2019-10-23): If Skolem locations can be substituted by anything,
             * then we may also not drop *concrete* update!
             */
            if (abstrUpd.assignsNothing() // nothing is always OK to remove
                    || (!abstrUpd.assignsAllLocs() // should not assign everything
                            /*
                             * we don't know what the Skolem locations stand for, also stop if
                             * they're present
                             */
                            && !abstrUpd.getHasToAssignables().stream()
                                    .anyMatch(SkolemLoc.class::isInstance)
                            && !abstrUpd.getMaybeAssignables().stream()
                                    .anyMatch(SkolemLoc.class::isInstance)
                            && !containsAbstractStatementUsingLHS(target, nonexistingPV,
                                    services))) {
                return Optional.of(tb.skip());
            } else {
                return Optional.empty();
            }
        }

        return Optional.empty();
    }

    /**
     * Returns either a SKIP update if the elementary update <code>update</code> can
     * be dropped (which is the case if it assigns a variable that is not relevant),
     * or an empty optional if it assigns a relevant variable. In that case, as a
     * <strong>side effect</strong>, that variable is removed from the set of
     * relevant variables, since it's overwritten.
     * 
     * @param update   The elementary update to check.
     * @param target   The target formula, for extracting locations.
     * @param services The {@link Services} object.
     * @return The simplified update {@link Term}, or {@link Optional#empty()}.
     */
    private static Optional<Term> maybeDropElementaryUpdate(final Term update, final Term target,
            final Set<LocationVariable> relevantVars, final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final ElementaryUpdate eu = (ElementaryUpdate) update.op();
        final LocationVariable lhs = (LocationVariable) eu.lhs();
        if (relevantVars.contains(lhs)) {

            relevantVars.remove(lhs); // SIDE EFFECT!

            /* NOTE: Cannot discard updates of the form x:=x, see bug #1269 (MU, CS) */
            return Optional.empty();
        } else {
            // TODO Remove, those vars should be in relevantVars
            /*
             * In the standard case, we can drop the update here. However, if the target
             * contains abstract programs that might access the left-hand-side of this
             * update, we have to keep it.
             */
            if (!containsAbstractStatementUsingLHS(target, lhs, services)) {
                return Optional.of(tb.skip());
            } else {
                return Optional.empty();
            }
        }
    }

    /*
     * TODO (DS, 2019-01-04): Maybe we actually don't need this, since when
     * collecting variables in a JavaBlock, also the variables in the contracts
     * should be collected for an abstract placeholder statement...
     */
    private static boolean containsAbstractStatementUsingLHS(Term target, LocationVariable lhs,
            Services services) {
        final ContainsAbstractStatementUsingLHSVisitor visitor = //
                new ContainsAbstractStatementUsingLHSVisitor(
                        MergeRuleUtils.getJavaBlockRecursive(target).program(), lhs, services);
        visitor.start();
        return visitor.result();
    }

    private static class ContainsAbstractStatementUsingLHSVisitor extends JavaASTVisitor {
        final LocationVariable lhs;
        final Services services;

        boolean result = false;

        public ContainsAbstractStatementUsingLHSVisitor(ProgramElement root, LocationVariable lhs,
                Services services) {
            super(root, services);
            this.services = services;
            this.lhs = lhs;
        }

        @Override
        protected void doDefaultAction(SourceElement node) {
            if (node instanceof AbstractPlaceholderStatement) {
                final List<Operator> accessibles = //
                        getAccessiblesFromAbstrPlaceholderStmt((AbstractPlaceholderStatement) node);

                /*
                 * The result should be true if (1) the lhs is contained in the accessibles of
                 * this abstract placeholder statement OR (2) the accessibles contain allLocs,
                 * then lhs is contained as a default.
                 */

                /*
                 * TODO (DS, 2019-01-14): That's a hack, having problems with renamings again...
                 */
                // if (accessibles.contains(lhs)) {
                if (accessibles.stream().anyMatch(
                        op -> op instanceof LocationVariable && op.name().equals(lhs.name()))) {
                    result = true;
                }

                if (accessibles.contains(services.getTypeConverter().getLocSetLDT().getAllLocs())) {
                    result = true;
                }
            }
        }

        public boolean result() {
            return result;
        }

        private List<Operator> getAccessiblesFromAbstrPlaceholderStmt(
                AbstractPlaceholderStatement aps) {
            final TypeConverter typeConverter = services.getTypeConverter();

            final List<BlockContract> contracts = //
                    AbstractExecutionContractUtils.getNoBehaviorContracts(aps, services);

            if (contracts.isEmpty()) {
                return Collections.singletonList(typeConverter.getLocSetLDT().getAllLocs());
            }

            final OpCollector opColl = new OpCollector();

            for (BlockContract contract : contracts) {
                /*
                 * TODO (DS, 2019-01-14): Might not be a good idea to loop over *all* contracts;
                 * however, it's not unsound since if we're too broad elementaries will *not* be
                 * dropped (although they could be), it's rather a completeness issue.
                 * Alternatively, we'd have to find the right contract for this position.
                 */
                final Term accessiblesTerm = contract
                        .getAccessibleClause(typeConverter.getHeapLDT().getHeap());
                accessiblesTerm.execPostOrder(opColl);
            }

            return opColl.ops().stream().filter(op -> op.arity() == 0).collect(Collectors.toList());
        }
    }

    @Override
    public String toString() {
        return "\\dropEffectlessElementaries(" + uSV + ", " + targetSV + ", " + resultSV + ")";
    }
}