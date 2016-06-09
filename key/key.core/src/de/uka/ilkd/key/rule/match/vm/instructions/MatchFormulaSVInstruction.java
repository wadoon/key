package de.uka.ilkd.key.rule.match.vm.instructions;

import org.key_project.common.core.logic.sort.Sort;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;

public class MatchFormulaSVInstruction extends MatchSchemaVariableInstruction<FormulaSV> {

    protected MatchFormulaSVInstruction(FormulaSV op) {
        super(op);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(JavaDLTerm subst, MatchConditions mc, Services services) {
        if (subst.sort() == Sort.FORMULA) {
            return addInstantiation(subst, mc, services);
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
