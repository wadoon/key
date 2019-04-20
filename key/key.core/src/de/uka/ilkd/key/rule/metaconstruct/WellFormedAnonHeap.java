package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class WellFormedAnonHeap extends AbstractTermTransformer {

    public WellFormedAnonHeap() {
        super(new Name("#wellFormedAnonHeap"), 1);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst,
            Services services) {

        final TermBuilder tb = services.getTermBuilder();
        Term wellFormedAnon = null;

        final Function anonHeapFunc = services.getNamespaces().functions()
                .lookup(term.sub(0).toString());
        final Term anonHeapTerm = tb.label(tb.func(anonHeapFunc),
                ParameterlessTermLabel.ANON_HEAP_LABEL);
        wellFormedAnon = LoopScopeTools.and(tb, wellFormedAnon,
                tb.wellFormed(anonHeapTerm));

        return wellFormedAnon;
    }
}