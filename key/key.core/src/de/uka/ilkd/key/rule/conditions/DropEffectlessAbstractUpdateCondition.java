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

package de.uka.ilkd.key.rule.conditions;

import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.ProgVarAndLocSetsCollector;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.AbstractUpdate;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Variable condition dropping abstract updates which only write to locations
 * that are not read afterward.
 *
 * @author Dominic Steinhoefel
 */
public final class DropEffectlessAbstractUpdateCondition
        implements VariableCondition {
    private final UpdateSV uSV;
    private final Term schematicTarget;

    public DropEffectlessAbstractUpdateCondition(UpdateSV u, Term x) {
        this.uSV = u;
        this.schematicTarget = x;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions mc, Services services) {
        final SVInstantiations svInst = mc.getInstantiations();
        final Term u = (Term) svInst.getInstantiation(uSV);

        final Term target = instSchematicTerm(schematicTarget, svInst, services);

        if (u == null || target == null
                || !(u.op() instanceof AbstractUpdate)) {
            return null;
        }

        if (target.isRigid()) {
            /*
             * TODO (DS, 2019-01-04): CHECK MATCHING FOR NONRIGID TERMS!
             * Actually, the taclets using this condition only match on nonrigid
             * targets. For some reason, however, this matching does not work
             * (i.e., the taclets are also applied to rigid targets). That
             * shouldn't do any harm, but we have other taclets for these cases.
             * We should in any case check why the matching does not work...
             */
            return null;
        }

        return dropEffectlessAbstractUpdate(u, target, services) ? mc : null;
    }

    /**
     * Instantiates a {@link Term} with potentially multiple
     * {@link SchemaVariable}s. Also works for {@link Term}s with none or only
     * one {@link SchemaVariable}.
     *
     * @param schematicTerm
     *            The {@link Term} to instantiate to a non-schematic one.
     * @param svInst
     *            The {@link SVInstantiations} with instantiations for the
     *            {@link SchemaVariable}s in the {@link Term}.
     * @param services
     *            The {@link Services} object for
     *            {@link TermBuilder}/{@link TermFactory}.
     * @return An instantiated {@link Term} or null if any of the contained
     *         {@link SchemaVariable}s does not have an instantiation.
     */
    private static Term instSchematicTerm(final Term schematicTerm,
            final SVInstantiations svInst, final Services services) {
        if (schematicTerm.op() instanceof SchemaVariable) {
            // Performance shortcut
            return (Term) svInst
                    .getInstantiation((SchemaVariable) schematicTerm.op());
        }

        final TermBuilder tb = services.getTermBuilder();
        final OpCollector opColl = new OpCollector();
        schematicTerm.execPostOrder(opColl);

        final Map<Term, Term> repls = opColl.ops().stream()
                .filter(SchemaVariable.class::isInstance)
                .map(SchemaVariable.class::cast)
                .collect(Collectors.toMap(sv -> tb.var(sv),
                        sv -> (Term) svInst.getInstantiation(sv)));

        if (repls.containsValue(null)) {
            // At least one uninstantiated SV
            return null;
        }
        else {
            final OpReplacer opRepl = //
                    new OpReplacer(repls, services.getTermFactory());
            return opRepl.replace(schematicTerm);
        }

    }

    public static boolean dropEffectlessAbstractUpdate(Term update, Term target,
            Services services) {
        // XXX (DS, 2019-02-01): The passed update can be a junctor, careful!
        final AbstractUpdate abstrUpd = (AbstractUpdate) update.op();

        final Set<Operator> opsInTarget = collectNullaryOps(target, services);
        final Set<Operator> opsInAssignable = //
                collectNullaryOps(abstrUpd.lhs(), services);
        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();

        if (opsInAssignable.size() == 1
                && opsInAssignable.contains(locSetLDT.getEmpty())) {
            return true;
        }

        if (opsInAssignable.contains(locSetLDT.getAllLocs())) {
            /*
             * If an abstract update may change all locations, then it is never
             * effectless...
             */
            return false;
        }

        if (opsInTarget.contains(locSetLDT.getAllLocs())) {
            /*
             * Here, there are several possibilities. One of those is that the
             * allLocs locset occurs in the accessible part of an abstract
             * update or an abstract placeholder statement. In these cases, we
             * may not drop the update.
             *
             * TODO (DS, 2019-01-04): We might want to rule out the case that
             * the allLocs occurs in the *assignable* part of a subsequent
             * abstract update (and nowhere else, or only in other such safe
             * places), in that case, we can drop the update.
             */
            return false;
        }

        return opsInTarget.stream()
                .noneMatch(op -> opsInAssignable.contains(op));
    }

    @Override
    public String toString() {
        return String.format("\\dropEffectlessAbstractUpdate(%s, %s)", uSV,
                schematicTarget);
    }

    public static Set<Operator> collectNullaryOps(Term t, Services services) {
        TermNullaryOpCollector collector = new TermNullaryOpCollector(services);
        t.execPostOrder(collector);
        return collector.result();
    }

    private static class TermNullaryOpCollector extends DefaultVisitor {
        private final Set<Operator> result = new LinkedHashSet<>();
        private final Services services;

        public TermNullaryOpCollector(Services services) {
            this.services = services;
        }

        @Override
        public void visit(Term t) {
            if (t.op().arity() == 0) {
                result.add(t.op());
            }

            if (!t.javaBlock().isEmpty()) {
                final ProgVarAndLocSetsCollector pvc = //
                        new ProgVarAndLocSetsCollector( //
                                t.javaBlock().program(), services);
                pvc.start();
                result.addAll(pvc.result());
            }
        }

        public Set<Operator> result() {
            return result;
        }
    }
}