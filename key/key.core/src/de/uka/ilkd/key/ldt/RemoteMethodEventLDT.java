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
	private final Function evGetDir;
	private final Function evGetType;
	private final Function evGetPartner;
	private final Function evGetMethod;
	private final Function evGetArgs;
	private final Function evGetHeap;
	private final Function evIncoming;
	private final Function evOutgoing;
	private final Function evCall;
	private final Function evTerm;

	//history (of Remote method events) ... copy of: key.core/resources/de/uka/ilkd/key/proof/rules/events.key -> Seq hist;
	private LocationVariable hist;

	public RemoteMethodEventLDT (TermServices services) {
		super(NAME, services);
		evConst = addFunction(services, "event");
		evGetDir = addFunction(services, "getDirectionFromEvent");
		evGetType = addFunction(services, "getTypeFromEvent");
		evGetPartner = addFunction(services, "getPartnerFromEvent");
		evGetMethod = addFunction(services, "getMethodFromEvent");
		evGetArgs = addFunction(services, "getArgumentsFromEvent");
		evGetHeap = addFunction(services, "getHeapFromEvent");
		evIncoming = addFunction(services, "incoming");
		evOutgoing = addFunction(services, "outgoing");
		evCall = addFunction(services, "methodCall");
		evTerm = addFunction(services, "methodTermination");
		hist = (LocationVariable) services.getNamespaces().programVariables().lookup(HIST_NAME);
	}

	public Function evConst() {
		return evConst;
	}

	public Function evGetDir() {
		return evGetDir;
	}

	public Function evGetType() {
		return evGetType;
	}

	public Function evGetPartner() {
		return evGetPartner;
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
	
	public Function evIncoming() {
		return evIncoming;
	}

	public Function evOutgoing() {
		return evOutgoing;
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

	//maybe put somewhere else?
	public Function getMethodIdentifier(MethodDeclaration md, TermServices services) {
	    Function f = (Function)services.getNamespaces().methodIdentifier().lookup(md.getProgramElementName());
	    if (f == null) {
	        //add the function
	        f = new Function(md.getProgramElementName(), (Sort)services.getNamespaces().sorts().lookup(METHOD_SORT));
	    }
	    return f;
	}

	// TODO KD i implement @Override Methods
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
		return null;
	}

	@Override
	public Function getFunctionFor(Operator op, Services services, ExecutionContext ec) {
		return null;
	}

	@Override
	public boolean hasLiteralFunction(Function f) {
		return false;
	}

	@Override
	public Expression translateTerm(Term t, ExtList children, Services services) {
		return null;
	}

	@Override
	public Type getType(Term t) {
		return null;
	}
}