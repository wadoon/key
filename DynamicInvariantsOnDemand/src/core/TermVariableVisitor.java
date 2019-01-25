package core;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;


public class TermVariableVisitor implements Visitor{
	public List<LocationVariable> variables = new ArrayList<LocationVariable>();

	@Override
	public boolean visitSubtree(Term visited) {
		// TODO Auto-generated method stub
		return true;
	}

	@Override
	public void visit(Term visited) {
		if (visited == null)
			return;
		Operator op = visited.op();
		if (op instanceof LocationVariable) {
			variables.add((LocationVariable) op);
		}
	}

	@Override
	public void subtreeEntered(Term subtreeRoot) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void subtreeLeft(Term subtreeRoot) {
		// TODO Auto-generated method stub
		
	}

}
