package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

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

        final MethodFrame mf = JavaTools.getInnermostMethodFrame(
                svInst.getContextInstantiation().contextProgram(), services);
        final Statement activeStmt = (Statement) JavaTools
                .getActiveStatement(JavaBlock.createJavaBlock(mf.getBody()));
        final LoopStatement loop = (LoopStatement) activeStmt;
        final Term properInvInst = services.getSpecificationRepository()
                .getLoopSpec(loop).getInvariant(services);

        return matchCond.setInstantiations( //
                svInst.add(inv, properInvInst, services));
    }

    @Override
    public String toString() {
        return "\\getInvariant(" + inv + ")";
    }
}
