package de.uka.ilkd.key.rule.match.vm.instructions;

import org.key_project.common.core.logic.Operator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.MatchConditions;

public interface MatchOperatorInstruction extends MatchInstruction {
    
    public MatchConditions match(Operator instantiationCandidate,  MatchConditions matchConditions, Services services);

}
