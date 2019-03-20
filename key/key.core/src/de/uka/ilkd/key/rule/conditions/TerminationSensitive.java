package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class TerminationSensitive implements VariableCondition {

    private final SchemaVariable ts;
    private final ModalOperatorSV x;

    public TerminationSensitive(SchemaVariable ts, ModalOperatorSV x) {
        this.ts = ts;
        this.x = x;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {

        SVInstantiations svInst = matchCond.getInstantiations();
        final TermBuilder tb = services.getTermBuilder();
        final boolean dia = ((Modality) svInst.getInstantiation(x))
                .terminationSensitive();

        svInst = svInst.add(ts, (dia ? tb.tt() : tb.ff()), services);
        return matchCond.setInstantiations(svInst);
    }

    @Override
    public String toString() {
        return "\\terminationSensitive(" + x + ")";
    }
}