package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopSpecification;

public class GetVariant extends AbstractTermTransformer {

    public GetVariant() {
        super(new Name("#getVariant"), 1);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst,
            Services services) {

        LoopSpecification spec = services.getSpecificationRepository()
                .getLoopSpec(LoopScopeTools.getLoopFromActiveStatement(svInst,
                        services));
        final TermBuilder tb = services.getTermBuilder();
        Term variantTerm = spec.getVariant(spec.getInternalSelfTerm(),
                spec.getInternalAtPres(), services);
        LocationVariable variantPV = (LocationVariable) services.getNamespaces()
                .programVariables().lookup("variant");
        final boolean dia = term.sub(0).equals(tb.tt());
        return dia ? tb.prec(variantTerm, tb.var(variantPV)) : tb.tt();
    }
}