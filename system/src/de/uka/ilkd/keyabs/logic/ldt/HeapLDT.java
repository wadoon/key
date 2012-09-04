// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.keyabs.logic.ldt;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.ldt.LDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.ExtList;


/**
 * LDT responsible for the "Heap" sort, and the associated "Field" sort. Besides
 * offering the usual LDT functionality, this class is also responsible for
 * creating and managing the constant symbols representing fields. 
 */
public final class HeapLDT extends LDT implements IHeapLDT {
    
    public static final Name NAME = new Name("Heap");    
        
    public static final Name SELECT_NAME = new Name("select");
    public static final Name STORE_NAME = new Name("store");
    public static final Name BASE_HEAP_NAME = new Name("heap");
    public static final Name[] VALID_HEAP_NAMES = { BASE_HEAP_NAME };


    
    //additional sorts
    private final Sort fieldSort;    
    
    //select/store
    private final SortDependingFunction select;
    private final Function store;
    private final Function anon;
    private final Function memset;
    
    //predicates
    private final Map<Sort,Function> wellFormed;    
    //private final Function acc;
    //private final Function reach;
    
    //heap pv
    private final ImmutableArray<LocationVariable> heaps;
    
    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    public HeapLDT(IServices services) {
	super(NAME, services);
	final Namespace sorts    = services.getNamespaces().sorts();
	final Namespace progVars = services.getNamespaces().programVariables();
	
        fieldSort         = (Sort) sorts.lookup(new Name("Field"));	
        select            = addSortDependingFunction(services, SELECT_NAME.toString());
        store             = addFunction(services, "store");
        anon              = addFunction(services, "anon");
        memset            = addFunction(services, "memset");
       // acc               = addFunction(services, "acc");
       // reach             = addFunction(services, "reach");
        heaps = new ImmutableArray<LocationVariable>(new LocationVariable[]{
                (LocationVariable) progVars.lookup(BASE_HEAP_NAME)
        });
        wellFormed = new LinkedHashMap<Sort,Function>();
        wellFormed.put((Sort)sorts.lookup(new Name("Heap")), addFunction(services, "wellFormed"));
    }
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //------------------------------------------------------------------------- 
    
    private String getFieldSymbolName(LocationVariable fieldPV) {
	if(fieldPV.isImplicit()) {
	    return fieldPV.name().toString();
	} else {
	    String fieldPVName = fieldPV.name().toString();
	    int index = fieldPV.toString().indexOf("::");
	    assert index > 0;
	    return fieldPVName.substring(0, index)
	    	   + "::$" 
	    	   + fieldPVName.substring(index + 2);
	}
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
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
    
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.keyabs.logic.ldt.IHeapLDT#getFieldSort()
     */
    @Override
    public Sort getFieldSort() {
	return fieldSort;
    }
    
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.keyabs.logic.ldt.IHeapLDT#getSelect(de.uka.ilkd.key.logic.sort.Sort, de.uka.ilkd.key.java.IServices)
     */
    @Override
    public Function getSelect(Sort instanceSort, IServices services) {
	return select.getInstanceFor(instanceSort, services);
    }
    
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.keyabs.logic.ldt.IHeapLDT#getSortOfSelect(de.uka.ilkd.key.logic.op.Operator)
     */
    @Override
    public Sort getSortOfSelect(Operator op) {
	if(op instanceof SortDependingFunction 
           && ((SortDependingFunction)op).isSimilar(select)) {
	   return ((SortDependingFunction)op).getSortDependingOn(); 
	} else {
	    return null;
	}
    }
    
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.keyabs.logic.ldt.IHeapLDT#getStore()
     */
    @Override
    public Function getStore() {
	return store;
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.keyabs.logic.ldt.IHeapLDT#getAnon()
     */
    @Override
    public Function getAnon() {
	return anon;
    }    
    
    
    public Function getMemset() {
	return memset;
    }         
        
    public Function getWellFormed(Sort sort) {
	return wellFormed.get(sort);
    }
    
    
  /*  public Function getAcc() {
	return acc;
    }
    
    
    public Function getReach() {
	return reach;
    }*/
    
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.keyabs.logic.ldt.IHeapLDT#getHeap()
     */
    @Override
    public LocationVariable getHeap() {
	return heaps.get(0);
    }
        
    /* (non-Javadoc)
     * @see de.uka.ilkd.keyabs.logic.ldt.IHeapLDT#getAllHeaps()
     */
    @Override
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

   /* public LocationVariable getHeap(String heapName) {
       
       if(TermBuilder.BASE_HEAP_NAME.equals(heapName)) {
         return heap;
       }else{
         assert TermBuilder.SAVED_HEAP_NAME.equals(heapName);
         return savedHeap;
       }
    }*/    
    
    /**
     * Given a "program variable" representing a field or a model field, 
     * returns the function symbol representing the same field. For
     * normal fields (Java or ghost fields), this function symbol is a 
     * constant symbol of type "Field". For model fields, it is an observer
     * function symbol. If the appropriate symbol does not yet exist in the 
     * namespace, this method creates and adds it to the namespace as a
     * side effect.
     */
    public Function getFieldSymbolForPV(LocationVariable fieldPV, 
	    				IServices services) {
	assert fieldPV.isMember();	
	
	final Name name = new Name(getFieldSymbolName(fieldPV));
	Function result = (Function) services.getNamespaces()
	                                     .functions()
	                                     .lookup(name);
	if(result == null) {
	    int index = name.toString().indexOf("::");
	    assert index > 0;
	    final Name kind = new Name(name.toString().substring(index + 2));
	    
	    SortDependingFunction firstInstance 
		= SortDependingFunction.getFirstInstance(kind, services);
	    if(firstInstance != null) {
		Sort sortDependingOn = fieldPV.getContainerType().getSort();		
		result = firstInstance.getInstanceFor(sortDependingOn, services);
	    } else {
		if(fieldPV.isModel()) {
		    result = new ObserverFunction(
			    		kind.toString(), 
			                fieldPV.sort(),
			                fieldPV.getKeYJavaType(),
			                targetSort(),
			                fieldPV.getContainerType(),
			                fieldPV.isStatic(),
			                new ImmutableArray<KeYJavaType>());
		} else {
		    result = new Function(name, 
				          fieldSort, 
				          new Sort[0], 
				          null,
				          true);
		}
		services.getNamespaces().functions().addSafely(result);
	    }
	}
	
	//sanity check
	if(fieldPV.isModel()) {
	    assert result instanceof ObserverFunction;
	} else {
	    assert !(result instanceof ObserverFunction);
	    assert result.isUnique()
	           : "field symbol is not unique: " + result;
	}
                       
        return result;
    }

    
    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, 
                                 Term[] subs, 
                                 Services services, 
                                 ExecutionContext ec) {
	return false;
    }
    

    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, 
                		 Term left, 
                		 Term right, 
                		 Services services, 
                		 ExecutionContext ec) {
	return false;
    }

    
    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, 
	    			 Term sub, 
	    			 IServices services, 
	    			 ExecutionContext ec) {
	return false;
    }


    @Override
    public Term translateLiteral(Literal lit, IServices services) {
	assert false;
	return null;
    }
    

    @Override
    public Function getFunctionFor(de.uka.ilkd.key.java.expression.Operator op, 
	    			   Services serv, 
	    			   ExecutionContext ec) {
	assert false;
	return null;
    }

    
    @Override
    public boolean hasLiteralFunction(Function f) {
	return false;
    }

    
    @Override
    public Expression translateTerm(Term t, ExtList children) {
	assert false;
	return null;
    }
    
    
    @Override
    public final Type getType(Term t) {
	assert false;
	return null;
    }


    @Override
    public Function getReach() {
	// TODO Auto-generated method stub
	return null;
    }


    @Override
    public Function getAcc() {
	// TODO Auto-generated method stub
	return null;
    }



}
