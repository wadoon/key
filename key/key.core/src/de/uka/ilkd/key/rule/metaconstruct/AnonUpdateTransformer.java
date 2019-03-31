package de.uka.ilkd.key.rule.metaconstruct;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;

public class AnonUpdateTransformer extends AbstractTermTransformer {

    public AnonUpdateTransformer() {
        super(new Name("#anonUpdateTransformer"), 4, Sort.UPDATE);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst,
            Services services) {

        final TermBuilder tb = services.getTermBuilder();
        LoopStatement loop = LoopScopeTools.getLoopFromActiveStatement(svInst,
                services);
        LoopSpecification spec = services.getSpecificationRepository()
                .getLoopSpec(loop);

        final Map<LocationVariable, Term> atPres = spec.getInternalAtPres();
        final List<LocationVariable> heapContext = HeapContext
                .getModHeaps(services, term.sub(0).equals(tb.tt()));
        final ImmutableSet<ProgramVariable> localOuts = MiscTools
                .getLocalOuts(loop, services);

        // Prepare variant
        final Term variant = //
                spec.getVariant(spec.getInternalSelfTerm(), atPres, services);
        final Term variantUpdate = LoopScopeTools.prepareVariant(term, variant,
                services);

        final Map<LocationVariable, Map<Term, Term>> heapToBeforeLoop = //
                new LinkedHashMap<LocationVariable, Map<Term, Term>>();
        Term beforeLoopUpdate = LoopScopeTools.createBeforeLoopUpdate(services,
                heapContext, localOuts, heapToBeforeLoop, term.sub(1));

        // Additional Heap Terms
        Term anonUpdate = LoopScopeTools.createLocalAnonUpdate(localOuts,
                services);

        final Map<LocationVariable, Term> mods = new LinkedHashMap<LocationVariable, Term>();

        heapContext.forEach(heap -> mods.put(heap, spec.getModifies(heap,
                spec.getInternalSelfTerm(), atPres, services)));

        for (LocationVariable heap : heapContext) {
            final Term heapAnonUpdate = LoopScopeTools.createAnonUpdate(heap,
                    mods.get(heap), spec, services, term.sub(2));
            anonUpdate = tb.parallel(anonUpdate, heapAnonUpdate);
        }
        // END Additional Heap Terms

        final Term newFormula = tb.parallel(
                tb.parallel(beforeLoopUpdate, anonUpdate), variantUpdate);

        return newFormula;
    }
}