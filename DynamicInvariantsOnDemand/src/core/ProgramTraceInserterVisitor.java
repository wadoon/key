package core;
import java.util.ArrayList;
import java.util.HashMap;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Operator;


public class ProgramTraceInserterVisitor implements Visitor{
	@Override
	public boolean visitSubtree(Term visited) {
		// TODO Auto-generated method stub
		return true;
	}

	@Override
	public void visit(Term visited) {
		System.out.println(visited.toString());
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
