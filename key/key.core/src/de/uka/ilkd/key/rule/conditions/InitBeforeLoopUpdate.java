// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.conditions;

import java.util.List;
import java.util.Optional;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.AbstractLoopInvariantRule;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.util.MiscTools;

/**
 * Initializes the "before loop" update needed for the assignable clause. Also
 * saves the value of local variables before execution, although it does not
 * seem that this is necessary (did so because the previous built-in invariant
 * rules also did it).
 * 
 * NOTE: The new program variables are *not* added to the namespaces. This has
 * to be done inside a term transformer. The task of creating them is still done
 * here as they're used in several transformers. The first of them has to
 * extract and add them.
 * 
 * @author Dominic Steinhoefel
 */
public class InitBeforeLoopUpdate implements VariableCondition {
    private final SchemaVariable storeInSV;
    private final SchemaVariable termSV;

    public InitBeforeLoopUpdate(SchemaVariable resultVarSV, SchemaVariable termSV) {
        this.storeInSV = resultVarSV;
        this.termSV = termSV;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        if (svInst.getInstantiation(storeInSV) != null) {
            return matchCond;
        }

        // the target term should have a Java block
        final Term term = (Term) svInst.getInstantiation(termSV);
        if (term.javaBlock() == JavaBlock.EMPTY_JAVABLOCK) {
            return null;
        }

        final Operator op = term.op();
        assert op instanceof Modality;

        final ProgramElement pe = term.javaBlock().program();
        assert pe != null;
        assert pe instanceof StatementBlock;

        final Term beforeLoopUpdate = //
                createBeforeLoopUpdate(services,
                        HeapContext.getModHeaps(services,
                                isTransaction((Modality) op)),
                        MiscTools.getLocalOuts(pe, services));

        return matchCond.setInstantiations( //
                svInst.add(storeInSV, beforeLoopUpdate, services));
    }

    /**
     * Checks whether the given {@link Modality} is a transaction modality.
     * 
     * @param modality
     *            The modality to check.
     * @return true iff the given {@link Modality} is a transaction modality.
     */
    private static boolean isTransaction(final Modality modality) {
        return modality == Modality.BOX_TRANSACTION
                || modality == Modality.DIA_TRANSACTION;
    }

    /**
     * Creates the "...Before_LOOP" update needed for the assignable clause.
     * Copied from {@link AbstractLoopInvariantRule}.
     * 
     * @param services
     *            The {@link Services} object.
     * @param heapContext
     *            The relevant heap variables in the current context, which is
     *            the standard "heap" variable, and maybe more if transactions
     *            or permissions are activated.
     * @param localOuts
     *            The written local variables inside the loop visible to the
     *            outside.
     * @return The "...Before_LOOP" update needed for the assignable clause.
     */
    private static Term createBeforeLoopUpdate(Services services,
            final List<LocationVariable> heapContext,
            final ImmutableSet<ProgramVariable> localOuts) {
        final TermBuilder tb = services.getTermBuilder();

        Term beforeLoopUpdate = null;
        for (final LocationVariable heap : heapContext) {
            final LocationVariable lv = //
                    tb.heapAtPreVar(heap + "Before_LOOP", heap.sort(), true);

            final Term u = tb.elementary(lv, tb.var(heap));
            beforeLoopUpdate = Optional.ofNullable(beforeLoopUpdate)
                    .map(upd -> tb.parallel(upd, u)).orElse(u);
        }

        for (final ProgramVariable pv : localOuts) {
            final String pvBeforeLoopName = tb
                    .newName(pv.name().toString() + "Before_LOOP");
            final LocationVariable pvBeforeLoop = new LocationVariable(
                    new ProgramElementName(pvBeforeLoopName),
                    pv.getKeYJavaType());

            beforeLoopUpdate = tb.parallel(beforeLoopUpdate,
                    tb.elementary(pvBeforeLoop, tb.var(pv)));
        }

        return beforeLoopUpdate;
    }

    @Override
    public String toString() {
        return String.format( //
                "\\varcond (\\initBeforeLoopUpdate(%s, %s))", storeInSV, termSV);
    }

}
