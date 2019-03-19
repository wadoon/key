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
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.LoopSpecification;

/**
 * Expects a loop body and a Skolem constant "anon_heap_LOOP" for the anonymized
 * heap and creates the anonymizing update
 * <code>heap:=anon(heap, ..., anon_heap_LOOP)</code>.
 * 
 * @author Dominic Steinhoefel
 */
public final class CreateHeapAnonUpdate extends AbstractTermTransformer {

    public CreateHeapAnonUpdate() {
        super(new Name("#createHeapAnonUpdate"), 2);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst,
            Services services) {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();

        final Term target = term.sub(0);
        final Term anonHeap = term.sub(1);

        assert anonHeap.sort() == heapLDT.targetSort();

        // the target term should have a Java block
        if (target.javaBlock() == JavaBlock.EMPTY_JAVABLOCK) {
            return null;
        }

        assert target.op() instanceof Modality;
        final boolean isTransaction = target.op() == Modality.BOX_TRANSACTION
                || target.op() == Modality.DIA_TRANSACTION;

        final ProgramElement pe = target.javaBlock().program();

        assert pe != null;
        assert pe instanceof StatementBlock;
        assert ((StatementBlock) pe).getFirstElement() instanceof LoopStatement;

        final LoopStatement loop = //
                (LoopStatement) ((StatementBlock) pe).getFirstElement();

        final LoopSpecification loopSpec = //
                services.getSpecificationRepository().getLoopSpec(loop);

        final Term heapAnonUpdate = createHeapAnonUpdate(loopSpec,
                isTransaction, (Function) anonHeap.op(), services);

        return heapAnonUpdate;
    }

    /**
     * Computes the anonymized heap.
     */
    private static Term createHeapAnonUpdate(final LoopSpecification loopSpec,
            final boolean isTransaction, final Function anonHeapFunc,
            final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Term anonHeapTerm = tb.label(tb.func(anonHeapFunc),
                ParameterlessTermLabel.ANON_HEAP_LABEL);

        final Map<LocationVariable, Term> atPres = loopSpec.getInternalAtPres();
        final List<LocationVariable> heapContext = //
                HeapContext.getModHeaps(services, isTransaction);
        final Map<LocationVariable, Term> mods = new LinkedHashMap<>();
        heapContext.forEach(heap -> mods.put(heap, loopSpec.getModifies(heap,
                loopSpec.getInternalSelfTerm(), atPres, services)));

        Term anonHeapUpdate = tb.skip();
        for (LocationVariable heap : heapContext) {
            final Term mod = mods.get(heap);
            anonHeapUpdate = tb.parallel(anonHeapUpdate,
                    tb.strictlyNothing().equals(mod) ? tb.skip()
                            : tb.anonUpd(heap, mod, anonHeapTerm));
        }

        return anonHeapUpdate;
    }
}