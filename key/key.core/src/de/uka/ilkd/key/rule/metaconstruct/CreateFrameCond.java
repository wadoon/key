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

package de.uka.ilkd.key.rule.metaconstruct;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * Creates the frame condition (aka "assignable clause") for the given loop.
 * Also accepts the pre-state update and extracts the symbols from there. New
 * symbols in the pre-state update (like "heap_BeforeLOOP") are added to the
 * namespaces. This is because the update is, for the loop scope invariant
 * taclet, created by a variable condition; new symbols created there are not
 * automatically stored in the proof, or will be generated/stored multiple
 * times.
 * 
 * @author Dominic Steinhoefel
 */
public final class CreateFrameCond extends AbstractTermTransformer {

    public CreateFrameCond() {
        super(new Name("#createFrameCond"), 2);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst,
            Services services) {
        final Term loopFormula = term.sub(0);
        final Term beforeLoopUpdate = term.sub(1);

        // the target term should have a Java block
        if (loopFormula.javaBlock() == JavaBlock.EMPTY_JAVABLOCK) {
            return null;
        }

        assert loopFormula.op() instanceof Modality;
        final boolean isTransaction = loopFormula
                .op() == Modality.BOX_TRANSACTION
                || loopFormula.op() == Modality.DIA_TRANSACTION;

        final ProgramElement pe = loopFormula.javaBlock().program();

        assert pe != null;
        assert pe instanceof StatementBlock;
        assert ((StatementBlock) pe).getFirstElement() instanceof LoopStatement;

        final LoopStatement loop = //
                (LoopStatement) ((StatementBlock) pe).getFirstElement();

        final LoopSpecification loopSpec = //
                services.getSpecificationRepository().getLoopSpec(loop);

        final Map<LocationVariable, Map<Term, Term>> heapToBeforeLoopMap = //
                createHeapToBeforeLoopMap(beforeLoopUpdate, services);

        final Term frameCondition = createFrameCondition(loopSpec,
                isTransaction, heapToBeforeLoopMap, services);

        return frameCondition;
    }

    /**
     * Creates the frame condition.
     * 
     * @param loopSpec
     *            The {@link LoopSpecification}, for the modifies clause.
     * @param isTransaction
     *            A flag set to true iff the current modality is a transaction
     *            modality.
     * @param heapToBeforeLoopMap
     *            The map from heap variables to a map from original to
     *            pre-state terms.
     * @param services
     *            The {@link Services} object.
     * @return The frame condition.
     */
    private static Term createFrameCondition(final LoopSpecification loopSpec,
            final boolean isTransaction,
            final Map<LocationVariable, Map<Term, Term>> heapToBeforeLoopMap,
            final Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final Map<LocationVariable, Term> atPres = loopSpec.getInternalAtPres();
        final List<LocationVariable> heapContext = //
                HeapContext.getModHeaps(services, isTransaction);
        final Map<LocationVariable, Term> mods = new LinkedHashMap<>();
        heapContext.forEach(heap -> mods.put(heap, loopSpec.getModifies(heap,
                loopSpec.getInternalSelfTerm(), atPres, services)));

        Term frameCondition = null;
        for (LocationVariable heap : heapContext) {
            final Term mod = MiscTools.removeSingletonPVs(mods.get(heap),
                    services);
            final Term fc;

            if (tb.strictlyNothing().equals(mod)) {
                fc = tb.frameStrictlyEmpty(tb.var(heap),
                        heapToBeforeLoopMap.get(heap));
            }
            else {
                fc = tb.frame(tb.var(heap), heapToBeforeLoopMap.get(heap), mod);
            }

            frameCondition = frameCondition == null ? fc
                    : tb.and(frameCondition, fc);
        }

        return frameCondition;
    }

    /**
     * Extracts from the update saving the pre-state values the map from heap
     * variables to a map from original terms to the pre-state terms. Thereby,
     * saves the new variables in the namespaces (which should not have occurred
     * before!).
     * 
     * @param beforeLoopUpdate
     *            The update from new "before loop" PVs to the previous values.
     * @param services
     *            The {@link Services} object.
     * @return A map from heap variables to a map from original terms to the
     *         pre-state terms.
     */
    private Map<LocationVariable, Map<Term, Term>> createHeapToBeforeLoopMap(
            Term beforeLoopUpdate, Services services) {
        final Map<LocationVariable, Map<Term, Term>> result = //
                new LinkedHashMap<LocationVariable, Map<Term, Term>>();
        final TermBuilder tb = services.getTermBuilder();

        final List<Term> elems = MergeRuleUtils
                .getElementaryUpdates(beforeLoopUpdate, tb);

        for (final Term elem : elems) {
            final LocationVariable lhs = //
                    (LocationVariable) ((ElementaryUpdate) elem.op()).lhs();
            final Operator op = elem.sub(0).op();
            assert op instanceof LocationVariable;
            final LocationVariable rhs = (LocationVariable) op;

            services.getNamespaces().programVariables().addSafely(lhs);

            final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
            if (rhs.sort() == heapLDT.targetSort()) {
                put(result, rhs, elem.sub(0), tb.var(lhs));
            }
            else {
                put(result, heapLDT.getHeap(), elem.sub(0), tb.var(lhs));
            }
        }

        return result;
    }

    private static void put(Map<LocationVariable, Map<Term, Term>> map,
            LocationVariable key, Term t1, Term t2) {
        if (map.get(key) == null) {
            map.put(key, new LinkedHashMap<>());
        }
        map.get(key).put(t1, t2);
    }
}