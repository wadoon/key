package de.uka.ilkd.key.strategy.setHeuristics;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.ldt.LDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;

public class SetLDT extends LDT {

	public SetLDT(Name name, TermServices services) {
		super(name, services);
		// TODO Auto-generated constructor stub
	}

	public SetLDT(Name name, Sort targetSort, TermServices services) {
		super(name, targetSort, services);
		// TODO Auto-generated constructor stub
	}

	@Override
	public boolean isResponsible(Operator op, Term[] subs, Services services, ExecutionContext ec) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isResponsible(Operator op, Term left, Term right, Services services, ExecutionContext ec) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isResponsible(Operator op, Term sub, TermServices services, ExecutionContext ec) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Term translateLiteral(Literal lit, Services services) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Function getFunctionFor(Operator op, Services services, ExecutionContext ec) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean hasLiteralFunction(Function f) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Expression translateTerm(Term t, ExtList children, Services services) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Type getType(Term t) {
		// TODO Auto-generated method stub
		return null;
	}

	public Function getSingle() {
		// TODO Auto-generated method stub
		return null;
	}

}
