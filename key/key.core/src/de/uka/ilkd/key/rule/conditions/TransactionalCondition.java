package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class TransactionalCondition implements VariableCondition {

    private final SchemaVariable u;
    private final ModalOperatorSV x;

    public TransactionalCondition(SchemaVariable u, ModalOperatorSV x) {
        this.u = u;
        this.x = x;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {

        SVInstantiations svInst = matchCond.getInstantiations();
        TermBuilder tb = services.getTermBuilder();
        Modality m = (Modality) svInst.getInstantiation(x);
        Term t = (m == Modality.DIA_TRANSACTION
                || m == Modality.BOX_TRANSACTION) ? tb.tt() : tb.ff();
        svInst = svInst.add(u, t, services);
        return matchCond.setInstantiations(svInst);
    }

    @Override
    public String toString() {
        return "\\transactional(" + u + "," + x + ")";
    }
}