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

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.abstractexecution.java.AbstractProgramElement;
import de.uka.ilkd.key.abstractexecution.java.expression.AbstractExpression;
import de.uka.ilkd.key.abstractexecution.java.statement.AbstractStatement;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AllLocsLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.EmptyLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.HasToLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.IrrelevantAssignable;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.SkolemLoc;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.GenericTermReplacer;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * Utility functions for abstract execution.
 *
 * @author Dominic Steinhoefel
 */
public class AbstractExecutionUtils {
    /**
     * Applies the given update (concrete & in normal form!) to the target. This is
     * done by performing a simple substitution of left-hand sides for right-hand
     * sides, which is unsound if there may be modal operators in the target term.
     * So this method is only to be used in situations where this certainly is not
     * the case.
     * 
     * @param upd      The update to apply.
     * @param target   The target term.
     * @param services The {@link Services} object.
     * @return The term after update application.
     */
    public static Term applyUpdate(Term upd, Term target, Services services) {
        final TermBuilder tb = services.getTermBuilder();

        for (Term elemUpd : MergeRuleUtils.getElementaryUpdates(upd, tb)) {
            target = GenericTermReplacer.replace(target, //
                    t -> t.op() == ((ElementaryUpdate) elemUpd.op()).lhs(), //
                    t -> elemUpd.sub(0), //
                    services);
        }

        return target;
    }

    /**
     * @param updateTerm The term to check.
     * @return true iff the given {@link Term} contains an abstract update.
     */
    public static boolean containsAbstractUpdate(Term updateTerm) {
        final OpCollector opColl = new OpCollector();
        updateTerm.execPostOrder(opColl);
        return opColl.ops().stream().anyMatch(AbstractUpdate.class::isInstance);
    }

    /**
     * Checks whether the given {@link Term} is an abstract Skolem location set
     * value term. Those are {@link Term}s of the shape "value(someLocsetConstant)".
     * category. Also returns true for \value(allLocs)!
     * 
     * @param t        The {@link Term} to check.
     * @param services The {@link Services} object.
     * @return true iff the operator of <code>t</code> is an abstract Skolem
     *         location set.
     */
    public static boolean isAbstractSkolemLocationSetValueTerm(Term t, Services services) {
        return t.op() == services.getTypeConverter().getLocSetLDT().getValue();
    }

    /**
     * Abstract Skolem location sets are nullary constants of type LocSet.
     * 
     * @param op       The {@link Operator} to check.
     * @param services The {@link Services} object (for the {@link LocSetLDT}).
     * @return true iff the given operator is an abstract Skolem location set.
     */
    public static boolean isAbstractSkolemLocationSet(final Operator op, final Services services) {
        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        return op instanceof Function && op.arity() == 0
                && ((Function) op).sort() == locSetLDT.targetSort();
    }

    /**
     * Unwraps a {@link HasToLoc}. Returns the original loc if it's not a
     * {@link HasToLoc}.
     * 
     * @param loc The location to unwrap.
     * @return The unwrapped location.
     */
    public static AbstractUpdateLoc unwrapHasTo(AbstractUpdateLoc loc) {
        if (loc instanceof HasToLoc) {
            return ((HasToLoc<?>) loc).child();
        }

        return loc;
    }

    /**
     * Unwraps all {@link HasToLoc} of the given {@link AbstractUpdate}, returns
     * them as a list.
     * 
     * @param abstrUpd The {@link AbstractUpdate} for which to return the unwrapped
     *                 locations.
     * @return The unwrapped locations.
     */
    public static List<AbstractUpdateLoc> unwrapHasTos(AbstractUpdate abstrUpd) {
        return abstrUpd.getAllAssignables().stream().map(AbstractExecutionUtils::unwrapHasTo)
                .collect(Collectors.toList());
    }

    /**
     * Creates an artificial {@link StatementBlock} for the given
     * {@link AbstractProgramElement}, since we re-use the existing block contract
     * architecture --- and thus need blocks...
     * 
     * @param abstractStmt The APE for which to create a {@link StatementBlock}
     * @return The {@link StatementBlock}
     */
    public static StatementBlock createArtificialStatementBlockForAPE(
            AbstractStatement abstractStmt) {
        final ExtList children = new ExtList(abstractStmt.getComments());
        children.add(abstractStmt);
        children.add(abstractStmt.getPositionInfo());
        return new StatementBlock(children, true);
    }

    /**
     * Creates an artificial {@link StatementBlock} for the given
     * {@link AbstractProgramElement}, since we re-use the existing block contract
     * architecture --- and thus need blocks...
     * 
     * @param abstractExpr The APE for which to create a {@link StatementBlock}
     * @param services     The {@link Services} object.
     * @return The {@link StatementBlock}
     */
    public static StatementBlock createArtificialStatementBlockForAPE( //
            AbstractProgramElement ape, Services services) {
        return ape instanceof AbstractStatement
                ? AbstractExecutionUtils
                        .createArtificialStatementBlockForAPE((AbstractStatement) ape)
                : AbstractExecutionUtils.createArtificialStatementBlockForAPE(
                        (AbstractExpression) ape, services.getJavaInfo().getJavaLangObject());
    }

    /**
     * Creates an artificial {@link StatementBlock} for the given
     * {@link AbstractProgramElement}, since we re-use the existing block contract
     * architecture --- and thus need blocks...
     * 
     * @param abstractExpr The APE for which to create a {@link StatementBlock}
     * @param kjt          The type of the {@link AbstractExpression} target.
     * @return The {@link StatementBlock}
     */
    public static StatementBlock createArtificialStatementBlockForAPE(
            AbstractExpression abstractExpr, KeYJavaType kjt) {
        return createArtificialStatementBlockForAPE(abstractExpr, kjt, null);
    }

    /**
     * Creates an artificial {@link StatementBlock} for the given
     * {@link AbstractProgramElement}, since we re-use the existing block contract
     * architecture --- and thus need blocks...
     * 
     * @param abstractExpr The APE for which to create a {@link StatementBlock}
     * @param sort         The sort of the {@link AbstractExpression} target. Prefer
     *                     {@link #createArtificialStatementBlockForAPE(AbstractExpression, KeYJavaType)}
     *                     whenever a {@link KeYJavaType} is available.
     * @return The {@link StatementBlock}
     */
    public static StatementBlock createArtificialStatementBlockForAPE(
            AbstractExpression abstractExpr, Sort sort) {
        return createArtificialStatementBlockForAPE(abstractExpr, null, sort);
    }

    /**
     * Creates an artificial {@link StatementBlock} for the given
     * {@link AbstractProgramElement}, since we re-use the existing block contract
     * architecture --- and thus need blocks...
     * 
     * @param abstractExpr The APE for which to create a {@link StatementBlock}
     * @param kjt          The type of the {@link AbstractExpression} target.
     * @param sort         Optional sort, if kjt not known.
     * @return The {@link StatementBlock}
     */
    public static StatementBlock createArtificialStatementBlockForAPE(
            AbstractExpression abstractExpr, KeYJavaType kjt, Sort sort) {
        final LocationVariable dummyVar = //
                kjt == null ? new LocationVariable(new ProgramElementName("dummy"), sort)
                        : new LocationVariable(new ProgramElementName("dummy"), kjt);
        final Assignment assign = new CopyAssignment(dummyVar, (AbstractExpression) abstractExpr);

        final ExtList children = new ExtList(abstractExpr.getComments());
        children.add(assign);
        children.add(abstractExpr.getPositionInfo());

        return new StatementBlock(children, true);
    }

    /**
     * Returns, for an artificial {@link StatementBlock} (see, e.g.,
     * {@link #createArtificialStatementBlockForAPE(AbstractStatement)}), the actual
     * {@link AbstractProgramElement}, if any.
     * 
     * @param block The artificial {@link StatementBlock} (if it's not a
     *              StatementBlock, this method always returns an empty Optional).
     * @return The {@link AbstractProgramElement} contained.
     */
    public static Optional<AbstractProgramElement> getAPEFromArtificialBlock(Statement stmt) {
        if (!(stmt instanceof StatementBlock)) {
            return Optional.empty();
        }

        return getAPEFromArtificialBlock((StatementBlock) stmt);
    }

    /**
     * Returns, for an artificial {@link StatementBlock} (see, e.g.,
     * {@link #createArtificialStatementBlockForAPE(AbstractStatement)}), the actual
     * {@link AbstractProgramElement}, if any.
     * 
     * @param block The artificial {@link StatementBlock}.
     * @return The {@link AbstractProgramElement} contained.
     */
    public static Optional<AbstractProgramElement> getAPEFromArtificialBlock(StatementBlock block) {
        if (!block.isArtificialStatementBlock()) {
            return Optional.empty();
        }

        final ProgramElement firstChild = block.getChildAt(0);
        if (firstChild instanceof AbstractStatement) {
            return Optional.of((AbstractStatement) firstChild);
        } else if (firstChild instanceof CopyAssignment
                && ((CopyAssignment) firstChild).getChildAt(1) instanceof AbstractExpression) {
            return Optional.of((AbstractExpression) ((CopyAssignment) firstChild).getChildAt(1));
        }

        return Optional.empty();
    }

    /**
     * For location variables introduced fresh by KeY, there can be no disjointness
     * assumptions created a-priori. Therefore, this method checks whether the given
     * location variable loc is irrelevant for abstract location sets.
     * 
     * <p>
     * Pure method.
     * 
     * @param loc      The {@link AbstractUpdateLoc} to check.
     * @param goal     The context {@link Goal}.
     * @param services The {@link Services} object.
     * @return true iff loc is irrelevant for Skolem location sets since it is
     *         created fresh by KeY rules.
     */
    public static boolean locIsCreatedFresh(final AbstractUpdateLoc loc, final Goal goal,
            final Services services) {
        if (!(unwrapHasTo(loc) instanceof PVLoc)) {
            return false;
        }

        final LocationVariable locVar = ((PVLoc) unwrapHasTo(loc)).getVar();

        /*
         * Location variables that either are already present in the root sequent, or
         * are not related to the source, are considered fresh. Additionally, there is a
         * freshness flag for special variables like the exc, self and result variables
         * created in operation POs. We consider variables that don't have position
         * information as not related to the source. It would be soundness critical if
         * declarations of variables in the source code were not given position
         * information.
         */

        if (locVar.isFreshVariable()) {
            return true;
        }

        /*
         * NOTE (DS, 2019-11-18): If using the TermProgramVariableCollector, also
         * program variables occurring in the initial JavaBlock will be considered. This
         * isn't generally a bad idea; however, it's problematic with exception
         * variables in catch clauses which we anyway consider separately and don't want
         * to mess up the results for Skolem locset symbols. Everything of interest
         * (non-fresh) should be initialized in an update or so.
         */

//        final TermProgramVariableCollector collector = new TermProgramVariableCollector(
//                goal.getLocalSpecificationRepository(), services);
        final OpCollector collector = new OpCollector();

        StreamSupport.stream(goal.proof().root().sequent().spliterator(), true)
                .map(SequentFormula::formula).forEach(term -> term.execPostOrder(collector));
        if (collector.ops().contains(locVar)) {
            // Location was already present in the root node.
            return false;
        }

        return locVar.getPositionInfo() == PositionInfo.UNDEFINED
                || !locVar.getPositionInfo().startEndValid();
    }

    /**
     * Checks whether the given location is relevant w.r.t. the given set of
     * relevant locations. Returns null if the location is relevant, and a list of
     * formula positions used as evidence for irrelevance in the other case. The
     * returned list can be empty for trivial cases.
     * 
     * @param loc               The {@link AbstractUpdateLoc} to check for
     *                          relevance.
     * @param relevantLocations The relevant locations.
     * @param goal              The goal in which the {@link Rule} should be
     *                          applied.
     * @param services          The {@link Services} object.
     * @return true iff the given location is relevant w.r.t. the given set of
     *         relevant locations.
     */
    public static ImmutableList<PosInOccurrence> isRelevant(final AbstractUpdateLoc loc,
            final Collection<AbstractUpdateLoc> relevantLocations, final Goal goal,
            Services services) {
        return isRelevant(loc, relevantLocations, Collections.emptySet(), goal, services);
    }

    /**
     * Checks whether the given location is relevant w.r.t. the given set of
     * relevant and overwritten locations. Returns null if the location is relevant,
     * and a list of formula positions used as evidence for irrelevance in the other
     * case. The returned list can be empty for trivial cases.
     * 
     * @param loc                  The {@link AbstractUpdateLoc} to check for
     *                             relevance.
     * @param relevantLocations    The relevant locations.
     * @param overwrittenLocations A set of locations that are overwritten and
     *                             therefore definitely irrelevant.
     * @param goal                 The goal in which the {@link Rule} should be
     *                             applied.
     * @param services             The {@link Services} object.
     * @return true iff the given location is relevant w.r.t. the given set of
     *         relevant locations.
     */
    public static ImmutableList<PosInOccurrence> isRelevant(final AbstractUpdateLoc loc,
            final Collection<AbstractUpdateLoc> relevantLocations,
            final Collection<AbstractUpdateLoc> overwrittenLocations, final Goal goal,
            Services services) {
        final ImmutableSLList<PosInOccurrence> emptyList = ImmutableSLList.<PosInOccurrence>nil();
        ImmutableList<PosInOccurrence> result = emptyList;
        final AbstractUpdateLoc locUnwrapped = AbstractExecutionUtils.unwrapHasTo(loc);

        //@formatter:off
        /*
         * A location l1 (set) is *not* relevant w.r.t. another location l2 (set) if:
         * 
         * 1) l1 is overwritten, or there is no relevant location l2, or
         * 2) l1 is a PVLoc and l2 a different PVLoc, or
         * 3) l1 is not a PVLoc, and l2 is a fresh auxiliary program variable, or
         * 4) l1 is a fresh auxiliary program variable and l2 is an abstract location set, or
         * 5) there is evidence in the proof that l1 and l2 are disjoint.
         * 
         * In all other cases, l1 is relevant w.r.t. l2. It is relevant w.r.t. a set of
         * locations if it is relevant for any location in the set.
         * 
         * Case 4 is because the variable wouldn't be fresh if it was contained by the
         * possible instantiations of any abstract location set.
         */
        //@formatter:on

        if (loc instanceof IrrelevantAssignable || loc instanceof EmptyLoc
                || overwrittenLocations.contains(locUnwrapped) || relevantLocations.isEmpty()) {
            // Irrelevant, but no evidence needed
            return emptyList;
        }

        final Set<AbstractUpdateLoc> relevantLocsCopy = new LinkedHashSet<>(relevantLocations);
        if (locUnwrapped instanceof PVLoc) {
            // If loc is a PVLoc, we can safely remove all PVLocs that aren't equal.
            relevantLocsCopy.removeIf(ploc -> ploc instanceof PVLoc && !ploc.equals(locUnwrapped));
        } else {
            /*
             * Even if loc is allLocs, the "fresh" locations cannot be meant! We remove
             * them. They only should play a role if loc is a PVLoc.
             */
            relevantLocsCopy.removeIf(
                    ploc -> AbstractExecutionUtils.locIsCreatedFresh(ploc, goal, services));
        }

        relevantLocsCopy.removeIf(IrrelevantAssignable.class::isInstance);
        relevantLocsCopy.removeIf(EmptyLoc.class::isInstance);

        // loc has to be disjoint from *all* relevant locations.
        for (final AbstractUpdateLoc relevantLoc : relevantLocsCopy) {
            if ((relevantLoc instanceof AllLocsLoc || relevantLoc instanceof SkolemLoc)
                    && AbstractExecutionUtils.locIsCreatedFresh(locUnwrapped, goal, services)) {
                continue;
            }

            final Optional<PosInOccurrence> maybeIrrelevanceEvidence = //
                    isIrrelevant(locUnwrapped, relevantLoc, goal, services);

            if (maybeIrrelevanceEvidence.isPresent()) {
                result = result.append(maybeIrrelevanceEvidence.get());
            } else {
                // Relevant for this relevantLoc, return null
                return null;
            }
        }

        // Irrelevant --- return evidence
        return result;
    }

    /**
     * Looks in the antecedent of the given {@link Goal} for a premise asserting
     * that loc and relevantLoc are disjoint. The check is done syntactically for
     * performance reasons, but KeY should bring the disjointness assertions to a
     * normal form of the shape <code>loc1 \cap loc2 = {}</code>, therefore it
     * should be OK. There are no proofs involved.
     * 
     * <p>
     * Pure method.
     * 
     * @param loc         The location to check for relevance.
     * @param relevantLoc A location known to be relevant.
     * @param goal        The context {@link Goal}.
     * @param services    The {@link Services} object.
     * @return An empty {@link Optional} if it could not proven that loc is
     *         <em>not</em> relevant, and a premise proving the irrelevance (i.e.,
     *         disjointness) in the other case.
     */
    private static Optional<PosInOccurrence> isIrrelevant(final AbstractUpdateLoc loc,
            final AbstractUpdateLoc relevantLoc, final Goal goal, final Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final Term locsetDisjointTerm1 = tb.equals(
                tb.intersect(loc.toTerm(services), relevantLoc.toTerm(services)), tb.empty());
        final Term locsetDisjointTerm2 = tb.equals(
                tb.intersect(relevantLoc.toTerm(services), loc.toTerm(services)), tb.empty());

        for (SequentFormula premise : goal.sequent().antecedent()) {
            final Term premiseFor = premise.formula();
            if (premiseFor.equalsModIrrelevantTermLabels(locsetDisjointTerm1)
                    || premiseFor.equalsModIrrelevantTermLabels(locsetDisjointTerm2)) {
                return Optional.of(new PosInOccurrence(premise, PosInTerm.getTopLevel(), true));
            }
        }

        return Optional.empty();
    }
}
