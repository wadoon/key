package helperfunctions;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.util.Pair;


public class TermUpdateVisitor implements Visitor{
	// HashMap with Key: LHS, RHS: Variable Name, Value: Update Name
	// FIXME es k�nnen hier evtl auch mehrfache Zuweisungen zur gleichen Variable m�glich sein
	public LinkedList<Pair<String, String>> assignmentsLHS_RHS = new LinkedList<Pair<String, String>>();
	public LinkedHashSet<LocationVariable> LHSVariables = new LinkedHashSet<LocationVariable>();

	@Override
	public boolean visitSubtree(Term visited) {
		// TODO Auto-generated method stub
		return true;
	}
	
	@Override
	public void visit(Term visited) {
		// Beispielbaum:
//		parallel-upd(
//				parallel-upd(
//					parallel-upd(
//						parallel-upd(
//							elem-update(_x)(x),
//							elem-update(_y)(y)
//						),
//						elem-update(exc)(null)
//					),
//					elem-update(q)(Z(0(#)))
//				),
//				elem-update(r)(x)
//			)

		// Input Variablen: elem-update(_x)(x) -> visited.op == ElementaryUpdate, visited.op.lhs == _x, visited.op.sub(0).name == x
		// Andere: elem-update(q)(Z(0(#))) -> gleich
		// FIXME wie mit q dealen, ist atm q -> Z
		if (visited.op() instanceof ElementaryUpdate) {
			ElementaryUpdate elemOp = (ElementaryUpdate) visited.op();
			// Variable
			String variableName = elemOp.lhs().name().toString();
			
			if (variableName.contains("exc") || variableName.contains("heap"))
				return;
			
			String getsUpdatedWith;
			// Assignments like q = 0 | elem-update(q)(Z(0(#)))
			if (visited.sub(0).subs().size() > 0) {
				getsUpdatedWith = visited.sub(0).sub(0).op().name().toString();
			}
			// Assignments like _x = x | elem-update(_x)(x)
			else {
				getsUpdatedWith = visited.sub(0).op().name().toString();
			}	
			assignmentsLHS_RHS.add(new Pair<String, String>(variableName, getsUpdatedWith));
			LHSVariables.add((LocationVariable) elemOp.lhs());
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
