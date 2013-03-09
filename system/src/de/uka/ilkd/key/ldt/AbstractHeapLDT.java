package de.uka.ilkd.key.ldt;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.ExtList;
import de.uka.ilkd.keyabs.logic.ldt.IHeapLDT;

public abstract class AbstractHeapLDT extends LDT implements IHeapLDT {

    public static final Name NAME = new Name("Heap");    
    
    public static final Name SELECT_NAME = new Name("select");
    public static final Name BASE_HEAP_NAME = new Name("heap");
    
    //null
    private final Function nullFunc;
    
    
    //additional sorts
    private final Sort fieldSort;    
    
    //select/store
    protected final SortDependingFunction select;
    private final Function store;
    private final Function anon;
       

    //predicates
    private final Map<Sort,Function> wellFormed;    
    private final Function acc;
    private final Function reach;
    
    //heap pv
    private final ImmutableArray<LocationVariable> heaps;

    
    public AbstractHeapLDT(Name name, IServices services) {
	super(name, services);
	
	final Namespace<Sort> sorts    = services.getNamespaces().sorts();
	final Namespace<IProgramVariable> progVars = services.getNamespaces().programVariables();
	
        fieldSort         = sorts.lookup(new Name("Field"));	
        select            = addSortDependingFunction(services, SELECT_NAME.toString());
        store             = addFunction(services, "store");
        anon              = addFunction(services, "anon");
        nullFunc          = addFunction(services, "null");
        acc               = addFunction(services, "acc");
        reach             = addFunction(services, "reach");
        wellFormed = new LinkedHashMap<Sort,Function>();
        wellFormed.put(sorts.lookup(new Name("Heap")), addFunction(services, "wellFormed"));
        

        final Name[] validHeaps = getAllHeapNames();
        final LocationVariable[] heapVars = new LocationVariable[validHeaps.length];
        for (int i = 0; i<validHeaps.length; i++) {
            heapVars[i] = (LocationVariable) progVars.lookup(validHeaps[i]);
            assert heapVars[i] != null;
        }
        
        heaps = new ImmutableArray<LocationVariable>(heapVars);

    }

    /**
     * Given a constant symbol representing a field, this method returns a
     * simplified name of the constant symbol to be used for pretty printing.
     */
    public String getPrettyFieldName(Named fieldSymbol) {
        String name = fieldSymbol.name().toString();
        int index = name.indexOf("::");
        if(index == -1) {
            return name;
        } else {
            String result = name.substring(index + 2);
            if(result.charAt(0) == '$') {
        	result = result.substring(1);
            }
            return result;
        }
    }
    
    /**
     * Extracts the name of the enclosing class from the name of a constant
     * symbol representing a field.
     */
    public String getClassName(Function fieldSymbol) {
	String name = fieldSymbol.name().toString();
	int index = name.indexOf("::");
	if(index == -1) {
	    return null;
	} else {
	    return name.substring(0, index);
	}
    }


    /**
     * Returns the sort "Field".
     */
    public Sort getFieldSort() {
        return fieldSort;
    }

    /**
     * Returns the select function for the given sort.
     */
    public Function getSelect(Sort instanceSort, IServices services) {
        return select.getInstanceFor(instanceSort, services);
    }

    /**
     * If the passed operator is an instance of "select", this method returns
     * the sort of the function (identical to its return type); otherwise, 
     * returns null.
     */
    public Sort getSortOfSelect(Operator op) {
        if(op instanceof SortDependingFunction 
           && ((SortDependingFunction)op).isSimilar(select)) {
           return ((SortDependingFunction)op).getSortDependingOn(); 
        } else {
            return null;
        }
    }

    public Function getStore() {
        return store;
    }

    public Function getAnon() {
        return anon;
    }

    public Function getNull() {
        return nullFunc;
    }

    public Function getWellFormed(Sort sort) {
        return wellFormed.get(sort);
    }

    public Function getAcc() {
        return acc;
    }
    
    public Function getReach() {
        return reach;
    }

    public LocationVariable getHeap() {
        return heaps.get(0);
    }

    public ImmutableArray<LocationVariable> getAllHeaps() {
        return heaps;
    }

    public LocationVariable getHeapForName(Name name) {
        for (LocationVariable h : getAllHeaps()) {
            if (h.name().equals(name)) {
                return h;
            }
        }
        return null;
    }

    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, Term[] subs, Services services,
	    ExecutionContext ec) {
	        return false;
	    }

    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, Term left, Term right,
	    Services services, ExecutionContext ec) {
	        return false;
	    }

    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, Term sub, IServices services,
	    ExecutionContext ec) {
	        return false;
	    }

    @Override
    public Term translateLiteral(Literal lit, IServices services) {
        assert false;
        return null;
    }

    @Override
    public Function getFunctionFor(de.uka.ilkd.key.java.expression.Operator op, Services serv, ExecutionContext ec) {
        assert false;
        return null;
    }

    @Override
    public boolean hasLiteralFunction(Function f) {
        return false;
    }

    @Override
    public Expression translateTerm(Term t, ExtList children, IServices services) {
        assert false;
        return null;
    }

    @Override
    public final Type getType(Term t) {
        assert false;
        return null;
    }

    public abstract Name[] getAllHeapNames();
}