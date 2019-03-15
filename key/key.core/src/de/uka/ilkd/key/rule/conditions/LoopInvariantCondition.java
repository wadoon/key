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

public class LoopInvariantCondition implements VariableCondition {

    private final SchemaVariable inv;

    public LoopInvariantCondition(SchemaVariable inv) {
        this.inv = inv;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        if (svInst.getInstantiation(inv) != null) {
            return matchCond;
        }

        final Statement activeStmt = (Statement) JavaTools
                .getActiveStatement(
                        JavaBlock.createJavaBlock((StatementBlock) svInst
                                .getContextInstantiation().contextProgram()));
        final LoopStatement loop = (LoopStatement) activeStmt;
        final LoopSpecification loopSpec = //
                services.getSpecificationRepository().getLoopSpec(loop);
        
        if (loopSpec == null) {
            return null;
        }
        
        final Term properInvInst = loopSpec.getInvariant(services);
        
        if (properInvInst == null) {
            return null;
        }

        return matchCond.setInstantiations( //
                svInst.add(inv, properInvInst, services));
    }

    @Override
    public String toString() {
        return "\\getInvariant(" + inv + ")";
    }
}
