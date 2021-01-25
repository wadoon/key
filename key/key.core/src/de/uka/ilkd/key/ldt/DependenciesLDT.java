package de.uka.ilkd.key.ldt;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;

public class DependenciesLDT extends LDT {

	public static final Name NAME = new Name("EventMarker");    

	private final Function noR;
	private final Function noW;
	private final Function noRaW;
	private final Function noWaR;
	private final Function noWaW;
	private final Function rPred;
	private final Function wPred;


	public DependenciesLDT(TermServices services) {
		super(NAME, services);
		noR	         = addFunction(services, "noR");
		noW	         = addFunction(services, "noW");
		noRaW	         = addFunction(services, "noRaW");
		noWaR	         = addFunction(services, "noWaR");
		noWaW	         = addFunction(services, "noWaW");
		rPred	         = addFunction(services, "rPred");
		wPred	         = addFunction(services, "wPred");
	}

	public Function getNoR() {
		return noR;
	}

	public Function getNoW() {
		return noW;
	}

	public Function getNoRaW() {
		return noRaW;
	}

	public Function getNoWaR() {
		return noWaR;
	}

	public Function getNoWaW() {
		return noWaR;
	}
	
	public Function getRPred() {
		return rPred;
	}

	public Function getWPred() {
		return wPred;
	}

	@Override
	public boolean isResponsible(Operator op, Term[] subs, Services services, ExecutionContext ec) {
		return false;
	}

	@Override
	public boolean isResponsible(Operator op, Term left, Term right, Services services, ExecutionContext ec) {
		return false;
	}

	@Override
	public boolean isResponsible(Operator op, Term sub, TermServices services, ExecutionContext ec) {
		return false;
	}

	@Override
	public Term translateLiteral(Literal lit, Services services) {
		assert false;
		return null;
	}

	@Override
	public Function getFunctionFor(Operator op, Services services, ExecutionContext ec) {
		assert false;
		return null;
	}

	@Override
	public boolean hasLiteralFunction(Function f) {
		assert false;
		return false;
	}

	@Override
	public Expression translateTerm(Term t, ExtList children, Services services) {
		assert false;
		return null;
	}

	@Override
	public Type getType(Term t) {
		assert false;
		return null;
	}

}
