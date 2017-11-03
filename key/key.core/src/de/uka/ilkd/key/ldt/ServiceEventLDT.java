package de.uka.ilkd.key.ldt;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

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

public class ServiceEventLDT extends LDT {
	public static final Name NAME = new Name("Event");
	public static final Name HIST_NAME = new Name("hist");
	public static final Name INTERNAL_HIST_NAME = new Name("internalHist");
	public static final Name METHOD_SORT = new Name("MethodIdentifier");
	public static final Name ENVCALLER_NAME = new Name("environmentCaller");
	public static final Name CURRENT_PARAMS_NAME = new Name("currentParams");

	private final Function event;
	private final Function evType;
	private final Function evCaller;
	private final Function evCallee;
	private final Function evService;
	private final Function evContent;
	private final Function evHeap;
	private final Function serviceCall;
	private final Function serviceTerm;
	private final Function similarHist;
	private final Function similarEvent;
	private final Function similar;
	
    private final Function wellformedList;
    private final Function wellformedListCoop;
    
    private final Function coopListEquiv;
    private final Function equivHistory;
    private final Function equivEvent;
    private final Function invEvent;
    private final Function filterVisible;
    
    private final Function wellformedListInternal;
    private final Function wellformedListCoopInternal;
    
    private final Function coopListEquivInternal;
    private final Function equivHistoryInternal;
    private final Function filterVisibleInternal;
    
    private final Function equivEventLocal;
    private final Function equivEventGlobal;
    private final Function invEventLocal;
    private final Function invEventGlobal;
    private final Function isCallable;

    private final Function agreePreLocal;
    private final Function agreePreGlobal;
    private final Function agreePost;
    
    private final Function agreeBasic;


	//history (of Remote method events) ... copy of: key.core/resources/de/uka/ilkd/key/proof/rules/events.key -> Seq hist;
	private final LocationVariable hist;
	private final LocationVariable internalHist;
	private final LocationVariable environmentCaller;
	private final LocationVariable currentParams;
	
	private final Sort eventSort;
    private final Sort calltypeSort;
    private final Sort methodSort;


	public ServiceEventLDT (TermServices services) {
		super(NAME, services);
		event = addFunction(services, "event");
		evType = addFunction(services, "evType");
		evCaller = addFunction(services, "evCaller");
		evCallee = addFunction(services, "evCallee");
		evService = addFunction(services, "evService");
		evContent = addFunction(services, "evContent");
		evHeap = addFunction(services, "evHeap");
		serviceCall = addFunction(services, "serviceCall");
		serviceTerm = addFunction(services, "serviceTermination");
		similarHist = addFunction(services, "similarHist");
		similarEvent = addFunction(services, "similarEvent");
		similar = addFunction(services, "similar");
        wellformedList = addFunction(services, "wellformedList");
        wellformedListCoop = addFunction(services, "wellformedListCoop");        
        coopListEquiv = addFunction(services, "coopListEquiv");
        equivHistory = addFunction(services, "equivHistory");
        equivEvent = addFunction(services, "equivEvent");
        equivEventLocal = addFunction(services, "equivEventLocal");
        equivEventGlobal = addFunction(services, "equivEventGlobal");
        filterVisible = addFunction(services, "filterVisible");
        invEvent = addFunction(services, "invEvent");
        invEventLocal = addFunction(services, "invEventLocal");
        invEventGlobal = addFunction(services, "invEventGlobal");
        
        agreePreLocal = addFunction(services, "agreePreLocal");
        agreePreGlobal = addFunction(services, "agreePreGlobal");
        agreePost = addFunction(services, "agreePost");
        
        isCallable = addFunction(services, "isCallable");
        
        wellformedListInternal = addFunction(services, "wellformedListInternal");
        wellformedListCoopInternal = addFunction(services, "wellformedListCoopInternal");        
        coopListEquivInternal = addFunction(services, "coopListEquivInternal");
        equivHistoryInternal = addFunction(services, "equivHistoryInternal");
        filterVisibleInternal = addFunction(services, "filterVisibleInternal");
        agreeBasic = addFunction(services, "agreeBasic");

		hist = (LocationVariable) services.getNamespaces().programVariables().lookup(HIST_NAME);
		internalHist = (LocationVariable) services.getNamespaces().programVariables().lookup(INTERNAL_HIST_NAME);
		environmentCaller = (LocationVariable) services.getNamespaces().programVariables().lookup(ENVCALLER_NAME);
		currentParams = (LocationVariable) services.getNamespaces().programVariables().lookup(CURRENT_PARAMS_NAME);
		
		eventSort = (Sort) services.getNamespaces().sorts().lookup("Event");
		calltypeSort = (Sort) services.getNamespaces().sorts().lookup("EventType");
		methodSort = (Sort) services.getNamespaces().sorts().lookup(METHOD_SORT);
	}
	
	public Sort eventSort() {
	    return eventSort;
	}

	public Function eventConstructor() {
		return event;
	}

	public Function getTypeFromEvent() {
		return evType;
	}

	public Function getCallerFromEvent() {
		return evCaller;
	}

	public Function getCalleeFromEvent() {
		return evCallee;
	}

	public Function getServiceFromEvent() {
		return evService;
	}

	public Function getContentFromEvent() {
		return evContent;
	}

	public Function getHeapFromEvent() {
		return evHeap;
	}

	public Function serviceCallConstant() {
		return serviceCall;
	}

	public Function serviceTerminationConstant() {
		return serviceTerm;
	}

	public Function similarHist() {
		return similarHist;
	}

	public Function similarEvent() {
		return similarEvent;
	}

	public Function similar() {
		return similar;
	}

	public Function getWellformedList() {
        return wellformedList;
    }

    public Function getWellformedListCoop() {
        return wellformedListCoop;
    }

    public Function getCoopListEquiv() {
        return coopListEquiv;
    }

    public Function getEquivHistory() {
        return equivHistory;
    }

    public Function getEquivEvent() {
        return equivEvent;
    }

    public Function getInvEvent() {
        return invEvent;
    }

    public Function getFilterVisible() {
        return filterVisible;
    }

    /**
	 * @return the history of Remote method events;
	 */
	public LocationVariable getHist() {
		return hist;
	}
	

    public LocationVariable getInternalHist() {
        return internalHist;
    }

	public LocationVariable getEnvironmentCaller() {
		return environmentCaller;
	}

    public LocationVariable getCurrentParams() {
        return currentParams;
    }

	public Function getWellformedListInternal() {
        return wellformedListInternal;
    }

    public Function getWellformedListCoopInternal() {
        return wellformedListCoopInternal;
    }

    public Function getCoopListEquivInternal() {
        return coopListEquivInternal;
    }

    public Function getEquivHistoryInternal() {
        return equivHistoryInternal;
    }

    public Function getFilterVisibleInternal() {
        return filterVisibleInternal;
    }

    // maybe put somewhere else?
	public Function getMethodIdentifierByDeclaration(MethodDeclaration md, TermServices services) { // TODO KD z use more than just method name
	    String string = md.getFullName();
		return getMethodIdentifierByString(string, services);
	}
	public Function getMethodIdentifierByString(String string, TermServices services) {
		Name name = new Name(string);
		return getMethodIdentifierByName(name, services);
	}
	public Function getMethodIdentifierByName(Name name, TermServices services) {
	    Function f = (Function) services.getNamespaces().methodIdentifier().lookup(name);
	    if (f == null) {
	        //add the function
	        f = new Function(name, (Sort)services.getNamespaces().sorts().lookup(METHOD_SORT), new ImmutableArray<Sort>(), null, true);
	        services.getNamespaces().methodIdentifier().addSafely(f);
	    }
	    return f;
	}


	// TODO KD z add Operators / Literals / Types?

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
		assert false; // TODO KD z just to be sure
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

    public Sort getCalltypeSort() {
        return calltypeSort;
    }

    public Sort getMethodSort() {
        return methodSort;
    }
    
    public Function getIsCallable() {
        return isCallable;
    }

    public Function getAgreePreLocal() {
        return agreePreLocal;
    }

    public Function getAgreePreGlobal() {
        return agreePreGlobal;
    }

    public Function getAgreePost() {
        return agreePost;
    }

    public Function getAgreeBasic() {
        return agreeBasic;
    }

}