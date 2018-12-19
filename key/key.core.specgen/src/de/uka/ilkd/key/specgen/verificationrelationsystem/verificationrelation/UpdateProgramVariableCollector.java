package de.uka.ilkd.key.specgen.verificationrelationsystem.verificationrelation;

import java.util.HashSet;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.op.UpdateableOperator;

public class UpdateProgramVariableCollector extends DefaultVisitor {

	private boolean hasRun;
	private final HashSet<LocationVariable> myResult;

    public UpdateProgramVariableCollector() {
    	hasRun = false;
    	myResult = new LinkedHashSet<LocationVariable>();
    }
 
    public void visit(Term term) {
    	Operator currentOperator = term.op();
    	if( currentOperator instanceof LocationVariable ) {
    		LocationVariable locVar = (LocationVariable)currentOperator;
    		myResult.add( locVar );
    	} else if( currentOperator instanceof ElementaryUpdate ) {
    		ElementaryUpdate elemUpd = (ElementaryUpdate)currentOperator;
    		UpdateableOperator leftHandSide = elemUpd.lhs();
    		if(leftHandSide instanceof LocationVariable) {
    			LocationVariable locVar = (LocationVariable)leftHandSide;
    			myResult.add(locVar);
    		}
    	} else if( currentOperator instanceof UpdateJunctor ) {
    		for(int i=0; i<term.arity(); i++) {
    			Term currentSubterm = term.sub(i);
    			visit(currentSubterm);
    		}
    	}    	
    	hasRun = true;
    }

    public HashSet<LocationVariable> result() {
    	assert(hasRun);
    	return myResult;
    }

}
