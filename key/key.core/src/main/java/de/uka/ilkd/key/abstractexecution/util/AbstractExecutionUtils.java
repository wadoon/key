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

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.GenericTermReplacer;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
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
     * category.
     * 
     * @param t        The {@link Term} to check.
     * @param services The {@link Services} object.
     * @return true iff the operator of <code>t</code> is an abstract Skolem
     *         location set.
     */
    public static boolean isAbstractSkolemLocationSetValueTerm(Term t, Services services) {
        final Function locsetToValueFunction = services.getTypeConverter().getLocSetLDT()
                .getValue();
        return t.op() == locsetToValueFunction && //
                t.sub(0).op() instanceof Function && //
                t.sub(0).arity() == 0;
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
}
