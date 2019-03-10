package de.uka.ilkd.key.rule.metaconstruct;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableSet;

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
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;

public class GetFrameCondition extends AbstractTermTransformer {

    public GetFrameCondition() {
        super(new Name("#getFrameCondition"), 2);
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
        final ImmutableSet<ProgramVariable> localOuts = MiscTools
                .getLocalOuts(loop, services);

        final Map<LocationVariable, Map<Term, Term>> heapToBeforeLoop = //
                new LinkedHashMap<LocationVariable, Map<Term, Term>>();
        // Changes heapContext!
        LoopScopeTools.createBeforeLoopUpdate(services, heapContext, localOuts,
                heapToBeforeLoop, term.sub(1));

        // Additional Heap Terms
        final Map<LocationVariable, Term> mods = new LinkedHashMap<LocationVariable, Term>();
        heapContext.forEach(heap -> mods.put(heap, spec.getModifies(heap,
                spec.getInternalSelfTerm(), atPres, services)));

        Term frameCondition = null;

        for (LocationVariable heap : heapContext) {
            final Term m1 = mods.get(heap);
            final Term fc;

            if (tb.strictlyNothing().equals(m1)) {
                fc = tb.frameStrictlyEmpty(tb.var(heap),
                        heapToBeforeLoop.get(heap));
            }
            else {
                fc = tb.frame(tb.var(heap), heapToBeforeLoop.get(heap), m1);
            }

            frameCondition = LoopScopeTools.and(tb, frameCondition, fc);
        }
        // END Additional Heap Terms

        return frameCondition;
    }
}
