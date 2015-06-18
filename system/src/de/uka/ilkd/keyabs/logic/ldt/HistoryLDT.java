package de.uka.ilkd.keyabs.logic.ldt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.ldt.LDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.ExtList;
import de.uka.ilkd.keyabs.abs.ABSServices;

public class HistoryLDT extends LDT {

    private final Sort interfaceLabelSort;
    private final Sort classLabelSort;
    private final Sort methodLabelSort;
    private final Sort futureSort;
    private final LocationVariable history;
    private final Function wellFormed;
    private final Function invocationEvent;
    private final Function invocationReactionEvent;
    private final Function completionEvent;
    private final Function completionReactionEvent;

    
    // the event types
    private final Function eventTypeIEV;
    private final Function eventTypeIREV;
    private final Function eventTypeCEV;
    private final Function eventTypeCREV;
    
    public HistoryLDT(IServices services) {
        super(new Name("Seq"), services);

        interfaceLabelSort = services.getNamespaces().sorts()
                .lookup(new Name("ItfLabel"));
        classLabelSort = services.getNamespaces().sorts()
                .lookup(new Name("ClassLabel"));
        methodLabelSort = services.getNamespaces().sorts()
                .lookup(new Name("MethodLabel"));
        futureSort = services.getNamespaces().sorts()
                .lookup(new Name("Future"));

        history                 = (LocationVariable) services.getNamespaces().programVariables().lookup("history");
        wellFormed              = addFunction((Function) services.getNamespaces().functions().lookup("wfHist"));
        
        invocationEvent = addFunction((Function) services.getNamespaces().functions().lookup("invocEv"));
        invocationReactionEvent = addFunction((Function) services.getNamespaces().functions().lookup("invocREv"));
        completionEvent = addFunction((Function) services.getNamespaces().functions().lookup("compEv"));
        completionReactionEvent = addFunction((Function) services.getNamespaces().functions().lookup("compREv"));

        
        eventTypeIEV = addFunction((Function) services.getNamespaces().functions().lookup("iEv"));
        eventTypeIREV = addFunction((Function) services.getNamespaces().functions().lookup("iREv"));
        eventTypeCEV = addFunction((Function) services.getNamespaces().functions().lookup("cEv"));
        eventTypeCREV = addFunction((Function) services.getNamespaces().functions().lookup("cREv"));
        
    }

    @Override
    public boolean isResponsible(Operator op, Term[] subs, IServices services,
                                 ExecutionContext ec) {
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, Term left, Term right,
                                 IServices services, ExecutionContext ec) {
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, Term sub, IServices services,
                                 ExecutionContext ec) {
        return false;
    }

    @Override
    public Term translateLiteral(Literal lit, IServices services) {
        return null;
    }

    @Override
    public Function getFunctionFor(Operator op, IServices services,
                                   ExecutionContext ec) {
        return null;
    }

    @Override
    public boolean hasLiteralFunction(Function f) {
        return false;
    }

    @Override
    public Expression translateTerm(Term t, ExtList children, IServices services) {
        return null;
    }

    @Override
    public Type getType(Term t) {
        return null;
    }

    public Sort getInterfaceLabelSort() {
        return interfaceLabelSort;
    }

    public Sort getClassLabelSort() {
        return classLabelSort;
    }

    public Sort getMethodLabelSort() {
        return methodLabelSort;
    }

    public Sort getFutureSort() {
        return futureSort;
    }

    public Function getClassLabel(Name className, ABSServices services) {
        return (Function) services.getNamespaces().functions().lookup(className);
    }

    public LocationVariable getHistory() {
        return history;
    }

    public Function getWellFormed() {
        return wellFormed;
    }

    public Function getInvocationEvent() {
        return invocationEvent;
    }
    
    public Function getInvocationReactionEvent() {
        return invocationReactionEvent;
    }

    public Function getCompletionEvent() {
        return completionEvent;
    }
    
    public Function getCompletionReactionEvent() {
        return completionReactionEvent;
    }

    public Function getEventTypeForInvocationEvent() {
    	return eventTypeIEV;
    }
    
    public Function getEventTypeForInvocationReactionEvent() {
    	return eventTypeIREV;
    }
    
    public Function getEventTypeForCompletionEvent() {
    	return eventTypeCEV;
    }
    
    public Function getEventTypeForCompletionReactionEvent() {
    	return eventTypeCREV;
    }

	public Function getEventTypeOf(de.uka.ilkd.key.logic.op.Operator eventLabelOp) {
		Function result = null;
		if (eventLabelOp == invocationEvent) {
			result = eventTypeIEV;
		} else if (eventLabelOp == invocationReactionEvent) {
			result = eventTypeIREV;
		} else if (eventLabelOp == completionEvent) {
			result = eventTypeCEV;
		} else if (eventLabelOp == completionReactionEvent) {
			result = eventTypeCREV;
		}
		return result;
	}
}
