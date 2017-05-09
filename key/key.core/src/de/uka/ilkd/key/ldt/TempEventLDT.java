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
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;

public class TempEventLDT extends LDT {
    public static final Name NAME = new Name("Event");
    public static final Name HIST_NAME = new Name("hist");
    public static final Name HIST_A_NAME = new Name("hist_A");
    public static final Name HIST_B_NAME = new Name("hist_B");
    public static final Name METHOD_SORT = new Name("Method");
    public static final Name CURRENT_PARAMS_NAME = new Name("currentParams");

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
    
    private final Function wellformedList;
    private final Function wellformedListCoop;
    
    private final Function coopListEquiv;
    private final Function equivHistory;
    private final Function equivEvent;
    private final Function invEvent;
    private final Function filterVisible;
    
    private final LocationVariable currentParams;

    //history (of Remote method events) ... copy of: key.core/resources/de/uka/ilkd/key/proof/rules/events.key -> Seq hist;
    //TODO JK well, doesn't work if I put it there, in my case its in seq.key instead
    private final LocationVariable hist;
    
    private final LocationVariable hist_A;
    private final LocationVariable hist_B;
    private final LocationVariable environmentCaller;
   


    //TODO JK since we get a calltype from here, the sort I implemented isn't necessary anymore. Remove it!
    public TempEventLDT (TermServices services) {
        super(NAME, services);
        evConst = addFunction(services, "event");
        evGetDir = addFunction(services, "evDirection");
        evGetType = addFunction(services, "evCalltype");
        evGetPartner = addFunction(services, "evPartner");
        evGetMethod = addFunction(services, "evMethod");
        evGetArgs = addFunction(services, "evParams");
        
        evGetHeap = addFunction(services, "evHeap");
        
        evIncoming = addFunction(services, "in");
        evOutgoing = addFunction(services, "out");
        evCall = addFunction(services, "servcall");
        evTerm = addFunction(services, "servterm");
        
        wellformedList = addFunction(services, "wellformedList");
        wellformedListCoop = addFunction(services, "wellformedListCoop");
        
        coopListEquiv = addFunction(services, "coopListEquiv");
        equivHistory = addFunction(services, "equivHistory");
        equivEvent = addFunction(services, "equivEvent");
        filterVisible = addFunction(services, "filterVisible");
        invEvent = addFunction(services, "invEvent");
                
        hist = (LocationVariable) services.getNamespaces().programVariables().lookup(HIST_NAME);
        
        environmentCaller = (LocationVariable) services.getNamespaces().programVariables().lookup("environmentCaller");
        
        hist_A = (LocationVariable) services.getNamespaces().programVariables().lookup(HIST_A_NAME);
        hist_B = (LocationVariable) services.getNamespaces().programVariables().lookup(HIST_B_NAME);

        currentParams = (LocationVariable) services.getNamespaces().programVariables().lookup(CURRENT_PARAMS_NAME);

    }
    
    public LocationVariable getCurrentParams() {
        return currentParams;
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
    
    public LocationVariable getHist_A() {
        return hist_A;
    }
    
    public LocationVariable getHist_B() {
        return hist_B;
    }
    

    public Function wellformedList() {
        return wellformedList;
    }

    public Function wellformedListCoop() {
        return wellformedListCoop;
    }


    
    // TODO KD ask: is this the right place for the method?
    public Function getMethodIdentifier(MethodDeclaration md, TermServices services) {
        //TODO JK important! add class name to the identifier to prevent unnecessary ambiguity!
        Function f = (Function)services.getNamespaces().functions().lookup(md.getProgramElementName());

        if (f == null) {
            //add the function
            f = new Function(md.getProgramElementName(), (Sort)services.getNamespaces().sorts().lookup(METHOD_SORT));
            services.getNamespaces().functions().addSafely(f);
        }
        return f;
    }
    

    public Function coopListEquiv() {
        return coopListEquiv;
    }

    public Function equivHistory() {
        return equivHistory;
    }

    public Function equivEvent() {
        return equivEvent;
    }

    public Function filterVisible() {
        return filterVisible;
    }

    
    // TODO KD implement @Override Methods
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
        assert false;
        return null;
    }

    @Override
    public boolean hasLiteralFunction(Function f) {
        //return true if TranslateLiteral would work (I think)
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

    public Function invEvent() {
        return invEvent;
    }

    public LocationVariable getEnvironmentCaller() {
        return environmentCaller;
    }

}
