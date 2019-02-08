package core;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;


public class UpdateLHSCollectorVisitor implements Visitor{
	// Collects LocationVariables to which sth gets assigned to in an update (left hand side)
	// e.g elem-update(y)(x) -> y
	public List<LocationVariable> leftHandVariables = new ArrayList<LocationVariable>();

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
		if (op instanceof ElementaryUpdate) {
			ElementaryUpdate update = (ElementaryUpdate) op;
			if (update.lhs() instanceof LocationVariable) {
				leftHandVariables.add((LocationVariable) update.lhs());
			}
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
