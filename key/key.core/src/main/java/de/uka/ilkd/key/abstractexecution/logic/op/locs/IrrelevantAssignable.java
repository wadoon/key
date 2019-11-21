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
package de.uka.ilkd.key.abstractexecution.logic.op.locs;

import java.util.Collections;
import java.util.Set;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Used when simplifying {@link AbstractUpdate} assignables: If in the target of
 * an {@link AbstractUpdate} application U_P(loc1,loc2:=footprint) the location
 * loc2 does not occur, we replace it with an {@link IrrelevantAssignable}. Two
 * {@link IrrelevantAssignable}s are equal if they occur at the same position.
 * This is to enable unification of two different {@link AbstractUpdate}s of the
 * same type.
 * 
 * <p>
 * Only use via
 * {@link AbstractUpdateFactory#getIrrelevantAssignableForPosition(AbstractUpdate, int)},
 * do not instantiate directly.
 * 
 * @author Dominic Steinhoefel
 */
public class IrrelevantAssignable implements AbstractUpdateLoc {
    private final Term t;

    public IrrelevantAssignable(final Term t) {
        this.t = t;
    }

    @Override
    public Sort sort() {
        return t.sort();
    }

    @Override
    public Set<Operator> childOps() {
        return Collections.emptySet();
    }

    @Override
    public boolean mayAssign(AbstractUpdateLoc otherLoc, Services services) {
        return false;
    }

    @Override
    public boolean equals(Object obj) {
        return obj != null && obj instanceof IrrelevantAssignable
                && t.equals(((IrrelevantAssignable) obj).t);
    }

    @Override
    public int hashCode() {
        return 17 + 3 * t.hashCode();
    }

    @Override
    public Term toTerm(Services services) {
        return t;
    }

    @Override
    public String toString() {
        return t.toString();
    }

    @Override
    public boolean isAbstract() {
        return false;
    }

}
