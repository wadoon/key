package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopSpecification;

/**
 * TODO
 * 
 * @author Dominic Steinhoefel
 */
public class LoopVariantCondition implements VariableCondition {

    private final SchemaVariable variantSV;

    public LoopVariantCondition(SchemaVariable variantSV) {
        this.variantSV = variantSV;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        if (svInst.getInstantiation(variantSV) != null) {
            return matchCond;
        }

        final Statement activeStmt = (Statement) JavaTools.getActiveStatement(
                JavaBlock.createJavaBlock((StatementBlock) svInst
                        .getContextInstantiation().contextProgram()));
        final LoopStatement loop = (LoopStatement) activeStmt;
        final LoopSpecification loopSpec = //
                services.getSpecificationRepository().getLoopSpec(loop);

        if (loopSpec == null) {
            return null;
        }

        final Term variant = loopSpec.getVariant(loopSpec.getInternalSelfTerm(),
                loopSpec.getInternalAtPres(), services);

        if (variant == null) {
            return null;
        }

        return matchCond.setInstantiations( //
                svInst.add(variantSV, variant, services));
    }

    @Override
    public String toString() {
        return "\\getVariant(" + variantSV + ")";
    }
}
