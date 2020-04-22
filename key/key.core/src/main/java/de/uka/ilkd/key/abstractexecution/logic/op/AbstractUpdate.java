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

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import org.key_project.util.collection.UniqueArrayList;

import de.uka.ilkd.key.abstractexecution.java.AbstractProgramElement;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.EmptyLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.HasToLoc;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractSortedOperator;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Class of operators for abstract updates (in the sense of Abstract Execution),
 * i.e., updates of the form "U(assignables := accessibles)", where assignables
 * and accessibles are lists of {@link AbstractUpdateLoc} (generally, locations,
 * like location variables). The arity of these lists is fixed. Left-hand sides
 * will always be locations, right-hand sides are values that can be updated.
 * 
 * There is one such operator for every left hand side "assignables". Each of
 * these operator is unary, accepting a list "accessibles" of accessible
 * locations / terms (of fixed arity and sorts). Comparable to an
 * {@link ElementaryUpdate}.
 * 
 * {@link AbstractUpdate}s are immutable.
 */
public final class AbstractUpdate extends AbstractSortedOperator {

    private final AbstractProgramElement phs;

    /**
     * Assignables, both "has-to" and "maybe". Use {@link #getMaybeAssignables()} or
     * {@link #getHasToAssignables()} to get easier access to the two different
     * sorts of assignables. Should never be modified (create a new
     * {@link AbstractUpdate} to change the assignables).
     */
    private final UniqueArrayList<AbstractUpdateLoc> assignables;

    /**
     * The hash code of this {@link AbstractUpdate}; computed of the
     * {@link AbstractProgramElement} identifier and the left-hand side
     * (assignables).
     */
    private final int hashCode;

    /**
     * "Backup" of the Services object, s.t. it not always has to be provided when
     * only replacing program variables etc.
     */
    private final Services services;

    /**
     * Private constructor since there should be exactly one abstract update per
     * left-hand side, similarly as for {@link ElementaryUpdate}. Use
     * {@link #getInstance(AbstractProgramElement, Term, Optional)}.
     *
     * @param phs         The {@link AbstractProgramElement} for which this
     *                    {@link AbstractUpdate} should be created.
     * @param assignables The update's left-hand side (assignables).
     * @param services    The {@link Services} object.
     */
    AbstractUpdate(final AbstractProgramElement phs,
            final UniqueArrayList<AbstractUpdateLoc> assignables, final Sort[] argSorts,
            final Services services) {
        super(new Name("U_" + phs.getId() + "("
                + assignables.stream().map(lhs -> lhs.toString()).collect(Collectors.joining(","))
                + ")"), argSorts, Sort.UPDATE, false);

        this.services = services;
        this.phs = phs;
        this.assignables = assignables;
        this.hashCode = 5 + 17 * phs.getId().hashCode() + 27 * assignables.hashCode();
    }

    /**
     * Returns a new {@link AbstractUpdate} for the same
     * {@link AbstractProgramElement}, but with the given assignables set.
     * 
     * Only use {@link AbstractUpdateFactory#changeAssignables(AbstractUpdate, Map)}
     * or relatives, since
     * <ul>
     * <li>{@link AbstractUpdate}s are cached (otherwise, you get multiple instances
     * that look the same, but aren't, which can lead to problems in KeY---probably
     * completeness issues, only, however)</li>
     * <li>the order of assignables is important, and using this method in the wrong
     * way can have undesired results (also soundness issues!)</li>
     * </ul>
     * 
     *
     * @param newAssignables The new left-hand side for the {@link AbstractUpdate}.
     * @return A new {@link AbstractUpdate} with the given left-hand side.
     */
    AbstractUpdate changeAssignables(final UniqueArrayList<AbstractUpdateLoc> newAssignables) {
        return new AbstractUpdate( //
                phs, newAssignables, super.argSorts().toArray(new Sort[0]), services);
    }

    public AbstractProgramElement getAbstractPlaceholderStatement() {
        return this.phs;
    }

    public String getUpdateName() {
        /*
         * TODO (DS, 2019-01-03): There might be collisions here, ignoring for now...
         */
        return "U_" + phs.getId();
    }

    @Override
    public int hashCode() {
        return hashCode;
    }

    /**
     * Assignables, both "has-to" and "maybe". Unmodifiable. Use
     * {@link #getMaybeAssignables()} or {@link #getHasToAssignables()} to get
     * easier access to the two different sorts of assignables.
     *
     * @return All assignables.
     */
    public List<AbstractUpdateLoc> getAllAssignables() {
        return assignables;
    }

    /**
     * Assignables that may be assigned.
     *
     * @return The elements of the assignables union of this abstract update that
     *         may be assigned.
     */
    public Set<AbstractUpdateLoc> getMaybeAssignables() {
        return assignables.stream().filter(lhs -> !(lhs instanceof HasToLoc))
                .map(AbstractUpdateLoc.class::cast)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
    }

    /**
     * Assignables that have to be assigned. Removes the {@link HasToLoc} wrappers.
     *
     * @return The elements of the assignables union of this abstract update that
     *         have to be assigned.
     */
    public Set<AbstractUpdateLoc> getHasToAssignables() {
        return assignables.stream().filter(HasToLoc.class::isInstance).map(HasToLoc.class::cast)
                .map(HasToLoc::child).map(AbstractUpdateLoc.class::cast)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
    }
    /**
     * @return True iff this {@link AbstractUpdate} assigns no location at all.
     */
    public boolean assignsNothing() {
        // Second case should not happen.
        return assignables.isEmpty() || assignables.stream().allMatch(EmptyLoc.class::isInstance);
    }
}
