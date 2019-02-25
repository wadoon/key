package de.uka.ilkd.key.rule.metaconstruct;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.LoopSpecification;

public class WellFormedAnonHeap extends AbstractTermTransformer {

    public WellFormedAnonHeap() {
        super(new Name("#wellFormedAnonHeap"), 2);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst,
            Services services) {

        final TermBuilder tb = services.getTermBuilder();
        MethodFrame mf = JavaTools.getInnermostMethodFrame(
                svInst.getContextInstantiation().contextProgram(), services);
        Statement activeStmt = (Statement) JavaTools
                .getActiveStatement(JavaBlock.createJavaBlock(mf.getBody()));
        LoopStatement loop = (LoopStatement) activeStmt;
        LoopSpecification spec = services.getSpecificationRepository()
                .getLoopSpec(loop);

        final Map<LocationVariable, Term> atPres = spec.getInternalAtPres();
        Modality m = (Modality) term.sub(0).op();
        boolean transaction = (m == Modality.DIA_TRANSACTION
                || m == Modality.BOX_TRANSACTION);
        final List<LocationVariable> heapContext = HeapContext
                .getModHeaps(services, transaction);

        // Additional Heap Terms
        Term wellFormedAnon = null;

        final Map<LocationVariable, Term> mods = new LinkedHashMap<LocationVariable, Term>();
        heapContext.forEach(heap -> mods.put(heap, spec.getModifies(heap,
                spec.getInternalSelfTerm(), atPres, services)));

        for (LocationVariable heap : heapContext) {
            final LoopScopeTools.AnonUpdateData tAnon = LoopScopeTools
                    .createAnonUpdate(heap, mods.get(heap), spec, services,
                            term.sub(1));

            wellFormedAnon = LoopScopeTools.and(tb, wellFormedAnon,
                    tb.wellFormed(tAnon.anonHeap));
        }
        // END Additional Heap Terms

        return wellFormedAnon;
    }
}
