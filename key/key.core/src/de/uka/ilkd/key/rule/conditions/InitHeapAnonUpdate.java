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

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.LoopSpecification;

/**
 * Initializes the anonymizing update for the heap.
 * 
 * NOTE: The new function symbols are *not* added to the namespaces. This has to
 * be done inside a term transformer. The task of creating them is still done
 * here as they're used in several transformers. The first of them has to
 * extract and add them.
 * 
 * @author Dominic Steinhoefel
 */
public class InitHeapAnonUpdate implements VariableCondition {
    private final SchemaVariable storeInSV;
    private final SchemaVariable termSV;

    public InitHeapAnonUpdate(SchemaVariable resultVarSV,
            SchemaVariable termSV) {
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
        assert ((StatementBlock) pe).getFirstElement() instanceof LoopStatement;

        final LoopStatement loop = //
                (LoopStatement) ((StatementBlock) pe).getFirstElement();

        final LoopSpecification loopSpec = //
                services.getSpecificationRepository().getLoopSpec(loop);

        final Term anonHeapUpdate = //
                createHeapAnonUpdate(loopSpec, isTransaction((Modality) op),
                        services);

        return matchCond.setInstantiations( //
                svInst.add(storeInSV, anonHeapUpdate, services));
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
     * Creates the anonymizing update for the given loop specification.
     * 
     * @param loopSpec
     *            The {@link LoopSpecification}.
     * @param isTransaction
     *            set to true iff we're in a transaction modality (then, there
     *            are more heaps available).
     * @param services
     *            The {@link Services} object (for the {@link TermBuilder}).
     * @return The anonymizing update.
     */
    private static Term createHeapAnonUpdate(LoopSpecification loopSpec,
            boolean isTransaction, Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final Map<LocationVariable, Term> atPres = loopSpec.getInternalAtPres();
        final List<LocationVariable> heapContext = //
                HeapContext.getModHeaps(services, isTransaction);
        final Map<LocationVariable, Term> mods = new LinkedHashMap<>();
        heapContext.forEach(heap -> mods.put(heap, loopSpec.getModifies(heap,
                loopSpec.getInternalSelfTerm(), atPres, services)));

        Term anonUpdate = tb.skip();
        for (final LocationVariable heap : heapContext) {
            anonUpdate = tb.parallel(anonUpdate,
                    createElementaryAnonUpdate(heap, mods.get(heap), services));
        }

        return anonUpdate;
    }

    /**
     * Creates an elementary "heap := anon_heap_LOOP<<anonHeapFunction>>"
     * update.
     * 
     * @param heap
     *            The heap variable.
     * @param mod
     *            The modifies clause, only for checking whether it's strictly
     *            nothing (then the elementary update is a skip).
     * @param services
     *            The {@link Services} object (for the {@link TermBuilder}).
     * @return An elementary anonymizing heap update.
     */
    private static Term createElementaryAnonUpdate(LocationVariable heap,
            Term mod, Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final Name anonHeapName = new Name(
                tb.newName("anon_" + heap + "_LOOP"));
        final Function anonHeapFunc = new Function(anonHeapName, heap.sort());
        final Term anonHeapTerm = tb.label(tb.func(anonHeapFunc),
                ParameterlessTermLabel.ANON_HEAP_LABEL);

        return tb.strictlyNothing().equals(mod) ? tb.skip()
                : tb.anonUpd(heap, mod, anonHeapTerm);
    }

    @Override
    public String toString() {
        return String.format( //
                "\\varcond (\\initHeapAnonUpdate(%s, %s))", storeInSV, termSV);
    }

}
