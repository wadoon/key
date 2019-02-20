package de.uka.ilkd.key.rule.conditions;

import java.util.Map;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopSpecification;

public class LoopInvariantCondition implements VariableCondition {

    private final SchemaVariable inv;

    public LoopInvariantCondition(SchemaVariable inv) {
        this.inv = inv;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {

        SVInstantiations svInst = matchCond.getInstantiations();

        MethodFrame mf = JavaTools.getInnermostMethodFrame(
                svInst.getContextInstantiation().contextProgram(), services);
        Statement activeStmt = (Statement) JavaTools
                .getActiveStatement(JavaBlock.createJavaBlock(mf.getBody()));
        LoopStatement loop = (LoopStatement) activeStmt;
        LoopSpecification spec = services.getSpecificationRepository()
                .getLoopSpec(loop);
        final Map<LocationVariable, Term> atPres = spec.getInternalAtPres();
        Term properInvInst = spec.getInvariant(services);

        /*
         * final TermBuilder tb = services.getTermBuilder(); final Term variant
         * = spec.getVariant(spec.getInternalSelfTerm(), atPres, services);
         * 
         * final ProgramElementName variantName = new ProgramElementName(
         * tb.newName("variant")); final LocationVariable variantPV = new
         * LocationVariable(variantName, Sort.ANY);
         * 
         * properInvInst = tb.and(properInvInst, tb.prec(variant,
         * tb.var(variantPV)));
         */

        svInst = svInst.add(inv, properInvInst, services);
        return matchCond.setInstantiations(svInst);
    }

    @Override
    public String toString() {
        return "\\getInvariant(" + inv + ")";
    }
}
