package de.uka.ilkd.key.loopinvgen;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Reference;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractSortedOperator;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;

public class DependencePredicate extends AbstractSortedOperator {

	protected DependencePredicate(Name name, ImmutableArray<Sort> argSorts, Sort sort, boolean isRigid) {
		super(name, argSorts, sort, isRigid);
		// TODO Auto-generated constructor stub
	}

//	private final Name name;
//	private final int arity;
//	private final boolean isRigid;
//
//	public DependencePredicate(Name name, int arity, boolean isRigid, ImmutableArray<Reference> locs) {
//
//		this.name = name;
//		this.arity = arity;
//		this.isRigid = isRigid;
//	}
//
//	public final Name name() {
//		return name;
//	}
//	
//	@Override
//	public final int arity() {
//		return arity;
//	}
//	
//	@Override
//	public final boolean isRigid() {
//		return isRigid;
//	}
//
//	@Override
//	public Sort sort(ImmutableArray<Term> terms) {
//		return Sort.FORMULA;
//	}
//
//	@Override
//	public boolean bindVarsAt(int n) {
//		// TODO Auto-generated method stub
//		return false;
//	}
//
//	@Override
//	public boolean validTopLevel(Term term) {
//		// TODO Auto-generated method stub
//		return false;
//	}

}
