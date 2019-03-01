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

package de.uka.ilkd.key.abstractexecution.logic.op;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.abstractexecution.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstrUpdateLHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstrUpdateRHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AllLocsLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.EmptyLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.HasToLoc;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractSortedOperator;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Class of operators for abstract updates (in the sense of Abstract Execution),
 * i.e., updates of the form "U(LOCSET1 := LOCSET2)", where LOCSET1/2 are
 * location sets. There is one such operator for every left hand side "LOCSET1".
 * Each of these operator is unary, accepting a single argument "LOCSET2".
 * Comparable to an {@link ElementaryUpdate}.
 */
public final class AbstractUpdate extends AbstractSortedOperator {

    private final AbstractPlaceholderStatement phs;

    /**
     * Assignables, both "has-to" and "maybe". Use
     * {@link #getMaybeAssignables()} or {@link #getHasToAssignables()} to get
     * easier access to the two different sorts of assignables.
     */
    private final Set<AbstrUpdateLHS> assignables;

    /**
     * The hash code of this {@link AbstractUpdate}; computed of the
     * {@link AbstractPlaceholderStatement} identifier and the left-hand side
     * (assignables).
     */
    private final int hashCode;

    /**
     * "Backup" of the Services object, s.t. it not always has to be provided
     * when only replacing program variables etc.
     */
    private final Services services;

    /**
     * Private constructor since there should be exactly one abstract update per
     * left-hand side, similarly as for {@link ElementaryUpdate}. Use
     * {@link #getInstance(AbstractPlaceholderStatement, Term, ExecutionContext, Services)}.
     *
     * @param phs
     *            The {@link AbstractPlaceholderStatement} for which this
     *            {@link AbstractUpdate} should be created.
     * @param assignables
     *            The update's left-hand side (assignables).
     * @param services
     *            The {@link Services} object.
     */
    AbstractUpdate(final AbstractPlaceholderStatement phs,
            final Set<AbstrUpdateLHS> assignables, final Services services) {
        super(new Name("U_" + phs.getId() + "("
                + assignables.stream().map(lhs -> lhs.toString())
                        .collect(Collectors.joining(","))
                + ")"),
                new Sort[] {
                        services.getTypeConverter().getSetLDT().targetSort() },
                Sort.UPDATE, false);

        this.services = services;
        this.phs = phs;
        this.assignables = Collections.unmodifiableSet(assignables);
        this.hashCode = 5 + 17 * phs.getId().hashCode()
                + 27 * assignables.hashCode();
    }

    /**
     * Returns a new {@link AbstractUpdate} for the same
     * {@link AbstractPlaceholderStatement}, but with the given assignables set.
     * Should only be used by {@link AbstractUpdateFactory}, since
     * {@link AbstractUpdate}s are cached (otherwise, you get multiple instances
     * that look the same, but aren't, which can lead to problems in KeY).
     *
     * @param newAssignables
     *            The new left-hand side for the {@link AbstractUpdate}.
     * @return A new {@link AbstractUpdate} with the given left-hand side.
     */
    AbstractUpdate changeAssignables(final Set<AbstrUpdateLHS> newAssignables) {
        return new AbstractUpdate(phs, newAssignables, services);
    }

    public AbstractPlaceholderStatement getAbstractPlaceholderStatement() {
        return this.phs;
    }

    public String getUpdateName() {
        /*
         * TODO (DS, 2019-01-03): There might be collisions here, ignoring for
         * now...
         */
        return "U_" + phs.getId();
    }

    /**
     * Returns a new {@link AbstractUpdate} of this one with the
     * {@link ProgramVariable}s in the assignables replaced according to the
     * supplied map.
     *
     * @param replMap
     *            The replace map.
     * @return A new {@link AbstractUpdate} of this one with the
     *         {@link ProgramVariable}s in the assignables replaced according to
     *         the supplied map.
     */
    public AbstractUpdate replaceVariables(
            Map<ProgramVariable, ProgramVariable> replMap) {
        return new AbstractUpdate(phs,
                assignables.stream().map(lhs -> lhs.replaceVariables(replMap))
                        .map(AbstrUpdateLHS.class::cast)
                        .collect(Collectors
                                .toCollection(() -> new LinkedHashSet<>())),
                services);
    }

    @Override
    public int hashCode() {
        return hashCode;
    }

    /**
     * @return The left-hand side (assignables) as a {@link Term} (Set LDT).
     *         Prefer to work with the safer data structures in
     *         {@link #getAllAssignables()} etc. whenever possible.
     */
    public Term getLHSTerm() {
        final TermBuilder tb = services.getTermBuilder();
        return tb.setUnion(assignables.stream()
                .map(lhs -> lhs.toLHSTerm(services)).map(tb::setSingleton)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>())));
    }

    /**
     * Assignables, both "has-to" and "maybe". Unmodifiable. Use
     * {@link #getMaybeAssignables()} or {@link #getHasToAssignables()} to get
     * easier access to the two different sorts of assignables.
     *
     * @return All assignables.
     */
    public Set<AbstrUpdateLHS> getAllAssignables() {
        return assignables;
    }

    /**
     * Assignables that may be assigned.
     *
     * @return The elements of the assignables union of this abstract update
     *         that may be assigned.
     */
    public Set<AbstrUpdateRHS> getMaybeAssignables() {
        return assignables.stream().filter(lhs -> !(lhs instanceof HasToLoc))
                .map(AbstrUpdateRHS.class::cast)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
    }

    /**
     * Assignables that have to be assigned. Removes the {@link HasToLoc}
     * wrappers.
     *
     * @return The elements of the assignables union of this abstract update
     *         that have to be assigned.
     */
    public Set<AbstrUpdateRHS> getHasToAssignables() {
        return assignables.stream().filter(HasToLoc.class::isInstance)
                .map(HasToLoc.class::cast).map(HasToLoc::child)
                .map(AbstrUpdateRHS.class::cast)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
    }

    /**
     * @return true iff this abstract update assigns allLocs (i.e., all
     *         locations).
     */
    public boolean assignsAllLocs() {
        return assignables.stream().anyMatch(AllLocsLoc.class::isInstance);
    }

    /**
     * @param loc
     *            The {@link AbstractUpdateLoc}s to check.
     * @return true iff this {@link AbstractUpdate} may assign any of the given
     *         locations (includes "have-to"s).
     */
    public boolean mayAssignAny(Collection<AbstrUpdateRHS> loc) {
        return loc.stream().anyMatch(this::mayAssign);
    }

    /**
     * @param loc
     *            The {@link AbstractUpdateLoc} to check.
     * @return true iff this {@link AbstractUpdate} may assign the given
     *         location (includes "have-to"s).
     */
    public boolean mayAssign(AbstrUpdateRHS loc) {
        return getMaybeAssignables().stream().anyMatch(loc::equals)
                || getHasToAssignables().stream().anyMatch(loc::equals);
    }

    /**
     * @param loc
     *            The {@link AbstractUpdateLoc}s to check.
     * @return true iff this {@link AbstractUpdate} has to assign any of the
     *         given locations (includes "have-to"s).
     */
    public boolean hasToAssignAny(Collection<AbstrUpdateRHS> loc) {
        return loc.stream().anyMatch(this::hasToAssign);
    }

    /**
     * True if the given {@link AbstractUpdate} has to assign the given
     * location.
     *
     * @param loc
     * @return
     */
    public boolean hasToAssign(AbstrUpdateRHS loc) {
        return getHasToAssignables().stream().anyMatch(loc::equals);
    }

    /**
     * @return True iff this {@link AbstractUpdate} assigns no location at all.
     */
    public boolean assignsNothing() {
        // NOTE (DS, 2019-03-01): Second case shouldn't occur...
        return assignables.isEmpty()
                || assignables.stream().allMatch(EmptyLoc.class::isInstance);
    }
}