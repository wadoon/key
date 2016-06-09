package de.uka.ilkd.key.rule.match.vm.instructions;

import org.key_project.common.core.logic.op.QuantifiableVariable;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;

public class MatchVariableSVInstruction extends MatchSchemaVariableInstruction<VariableSV> {

    protected MatchVariableSVInstruction(VariableSV op) {
        super(op);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(JavaDLTerm subst, MatchConditions mc, Services services) {                
        if (subst.op() instanceof QuantifiableVariable) {
            final JavaDLTerm foundMapping = (JavaDLTerm) mc.getInstantiations().getInstantiation(op);
            if(foundMapping == null) {
                return addInstantiation(subst, mc, services);
            } else if (foundMapping.op() == subst.op()) {
                return mc;
            }
        }
        return null;        
    }

    @Override
    public MatchConditions match(TermNavigator termPosition, MatchConditions mc,
            Services services) {
        final MatchConditions result = match(termPosition.getCurrentSubterm(), mc, services);
        if (result != null) {
            termPosition.gotoNextSibling();
        }
        return result;           
    }

}
