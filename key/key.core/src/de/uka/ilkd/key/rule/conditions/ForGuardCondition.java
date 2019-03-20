package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.Guard;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class ForGuardCondition implements VariableCondition {

    private final ProgramSV guard;
    private final ProgramSV guardExpr;

    public ForGuardCondition(ProgramSV guardExpr, ProgramSV guard) {
        this.guard = guard;
        this.guardExpr = guardExpr;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {

        SVInstantiations svInst = matchCond.getInstantiations();

        svInst = svInst.add(guardExpr,
                ((Guard) svInst.getInstantiation(guard)).getExpression(),
                services);
        return matchCond.setInstantiations(svInst);
    }

    @Override
    public String toString() {
        return "\\getGuardExpr(" + guardExpr + "," + guard + ")";
    }
}