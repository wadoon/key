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

        SVInstantiations svInst = matchCond.getInstantiations();

        MethodFrame mf = JavaTools.getInnermostMethodFrame(
                svInst.getContextInstantiation().contextProgram(), services);
        Statement activeStmt = (Statement) JavaTools
                .getActiveStatement(JavaBlock.createJavaBlock(mf.getBody()));
        LoopStatement loop = (LoopStatement) activeStmt;
        Term properInvInst = services.getSpecificationRepository()
                .getLoopSpec(loop).getInvariant(services);

        svInst = svInst.add(inv, properInvInst, services);
        return matchCond.setInstantiations(svInst);
    }

    @Override
    public String toString() {
        return "\\getInvariant(" + inv + ")";
    }
}
