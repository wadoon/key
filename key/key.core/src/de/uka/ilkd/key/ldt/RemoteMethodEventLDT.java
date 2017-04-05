package de.uka.ilkd.key.ldt;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;

public class RemoteMethodEventLDT extends LDT {
	public static final Name NAME = new Name("Event");
	public static final Name HIST_NAME = new Name("hist");
	public static final Name METHOD_SORT = new Name("Method");

	private final Function evConst;
	private final Function evGetType;
	private final Function evGetCaller;
	private final Function evGetCallee;
	private final Function evGetMethod;
	private final Function evGetArgs;
	private final Function evGetHeap;
	private final Function evCall;
	private final Function evTerm;

	//history (of Remote method events) ... copy of: key.core/resources/de/uka/ilkd/key/proof/rules/events.key -> Seq hist;
	private LocationVariable hist;
	private LocationVariable caller;

	public RemoteMethodEventLDT (TermServices services) {
		super(NAME, services);
		evConst = addFunction(services, "event");
		evGetType = addFunction(services, "getTypeFromEvent");
		evGetCaller = addFunction(services, "getCallerFromEvent");
		evGetCallee = addFunction(services, "getCalleeFromEvent");
		evGetMethod = addFunction(services, "getMethodFromEvent");
		evGetArgs = addFunction(services, "getArgumentsFromEvent");
		evGetHeap = addFunction(services, "getHeapFromEvent");
		evCall = addFunction(services, "methodCall");
		evTerm = addFunction(services, "methodTermination");
		hist = (LocationVariable) services.getNamespaces().programVariables().lookup(HIST_NAME);
		caller = (LocationVariable) services.getNamespaces().programVariables().lookup("caller");
	}

	public Function evConst() {
		return evConst;
	}

	public Function evGetType() {
		return evGetType;
	}

	public Function evGetCaller() {
		return evGetCaller;
	}

	public Function evGetCallee() {
		return evGetCallee;
	}

	public Function evGetMethod() {
		return evGetMethod;
	}

	public Function evGetArgs() {
		return evGetArgs;
	}

	public Function evGetHeap() {
		return evGetHeap;
	}

	public Function evCall() {
		return evCall;
	}

	public Function evTerm() {
		return evTerm;
	}

	/**
	 * @return the history of Remote method events;
	 */
	public LocationVariable getHist() {
		return hist;
	}

	public LocationVariable getCaller() {
		return caller;
	}

	//maybe put somewhere else?
	public Function getMethodIdentifier(MethodDeclaration md, TermServices services) {
	    Function f = (Function)services.getNamespaces().methodIdentifier().lookup(md.getProgramElementName());
	    if (f == null) {
	        //add the function
	        f = new Function(md.getProgramElementName(), (Sort)services.getNamespaces().sorts().lookup(METHOD_SORT));
	    }
	    return f;
	}

	// TODO KD z add Operators / Literals / Types?
	// TODO KD s code review

	@Override
	public boolean isResponsible(Operator op, Term[] subs, Services services, ExecutionContext ec) {
		assert false : "RemoteMethodEventLDT: There are no Operatiors for Events.";
		return false; // add Operators to java.expression.operator.adt?
	}

	@Override
	public boolean isResponsible(Operator op, Term left, Term right, Services services, ExecutionContext ec) {
		assert false : "RemoteMethodEventLDT: There are no Operators for Events.";
		return false; // add Operators to java.expression.operator.adt?
	}

	@Override
	public boolean isResponsible(Operator op, Term sub, TermServices services, ExecutionContext ec) {
		assert false : "RemoteMethodEventLDT: There are no Operators for Events.";
		return false; // add Operators to java.expression.operator.adt?
	}

	@Override
	public Term translateLiteral(Literal lit, Services services) {
		assert false : "RemoteMethodEventLDT: There are no Literals for Events.";
		return null; // add Literals to java.expression.literal?
	}

	@Override
	public Function getFunctionFor(Operator op, Services services, ExecutionContext ec) {
		assert false : "RemoteMethodEventLDT: There are no Operators for Events.";
		return null; // add Operators to java.expression.operator.adt?
	}

	@Override
	public boolean hasLiteralFunction(Function f) {
		return containsFunction(f) && f.arity() == 0; // should return false I think
	}

	@Override
	public Expression translateTerm(Term t, ExtList children, Services services) {
		assert false : "RemoteMethodEventLDT: Could not translate Term: " + t;
		return null; // not sure if I can translate any terms at all
	}

	@Override
	public Type getType(Term t) {
		assert false : "RemoteMethodEventLDT: No Types are associated with Events.";
		return null; // add Types to java.abstraction.PrimitiveType?
	}
}