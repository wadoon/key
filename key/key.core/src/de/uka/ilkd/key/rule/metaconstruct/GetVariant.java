package de.uka.ilkd.key.rule.metaconstruct;

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
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopSpecification;

public class GetVariant extends AbstractTermTransformer {

    public GetVariant() {
        super(new Name("#getVariant"), 1);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst,
            Services services) {

        MethodFrame mf = JavaTools.getInnermostMethodFrame(
                svInst.getContextInstantiation().contextProgram(), services);
        Statement activeStmt = (Statement) JavaTools
                .getActiveStatement(JavaBlock.createJavaBlock(mf.getBody()));
        LoopStatement loop = (LoopStatement) activeStmt;

        LoopSpecification spec = services.getSpecificationRepository()
                .getLoopSpec(loop);

        final TermBuilder tb = services.getTermBuilder();
        Term variantTerm = spec.getVariant(spec.getInternalSelfTerm(),
                spec.getInternalAtPres(), services);
        if (variantTerm == null) {
            return tb.tt();
        }

        LocationVariable variantPV2 = (LocationVariable) services
                .getNamespaces().programVariables().lookup("variant");

        return tb.prec(variantTerm, tb.var(variantPV2));
    }
}
