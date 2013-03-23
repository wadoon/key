// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.util.ExtList;


/**
 * LDT responsible for the "Heap" sort, and the associated "Field" sort. Besides
 * offering the usual LDT functionality, this class is also responsible for
 * creating and managing the constant symbols representing fields. 
 */
public final class HeapLDT extends AbstractHeapLDT {
    
    private static final Name SAVED_HEAP_NAME = new Name("savedHeap");
    private static final Name[] VALID_HEAP_NAMES = { BASE_HEAP_NAME, SAVED_HEAP_NAME };
    
    //select/store
    private final Function create;
    private final Function memset;
    
    //fields
    private final Function arr;
    private final Function created;
    private final Function initialized;
    private final SortDependingFunction classPrepared;
    private final SortDependingFunction classInitialized;
    private final SortDependingFunction classInitializationInProgress;
    private final SortDependingFunction classErroneous;
    
    //length
    private final Function length;
    private static Name[] allValidHeapNames;

    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    public HeapLDT(IServices services) {
	super(NAME, services);

	    create            = addFunction(services, "create");
        memset            = addFunction(services, "memset");
        arr               = addFunction(services, "arr");
        created           = addFunction(services, "java.lang.Object::<created>");
        initialized       = addFunction(services, "java.lang.Object::<initialized>");
        classPrepared     = addSortDependingFunction(services, "<classPrepared>");
        classInitialized  = addSortDependingFunction(services, "<classInitialized>");
        classInitializationInProgress  
                          = addSortDependingFunction(services, "<classInitializationInProgress>");
        classErroneous    = addSortDependingFunction(services, "<classErroneous>");
        length            = addFunction(services, "length");        

    }

    public static Name[] getAllValidHeapNames() {
        return allValidHeapNames;
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
    @Override
    public Name[] getAllHeapNames() {
	return VALID_HEAP_NAMES;
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
    
    
    public Function getCreate() {
	return create;
    }
    
    
    public Function getMemset() {
	return memset;
    }     
    
    
    public Function getArr() {
	return arr;
    }
    
    
    public Function getCreated() {
	return created;
    }
    
    
    public Function getInitialized() {
	return initialized;
    }
    
        
    public Function getClassPrepared(Sort instanceSort, IServices services) {
	return classPrepared.getInstanceFor(instanceSort, services);
    }
    
    
    public Function getClassInitialized(Sort instanceSort, IServices services) {
	return classInitialized.getInstanceFor(instanceSort, services);
    }
    
    
    public Function getClassInitializationInProgress(Sort instanceSort, 
	    					     IServices services) {
	return classInitializationInProgress.getInstanceFor(instanceSort, 
							    services);
    }
    
    
    public Function getClassErroneous(Sort instanceSort, IServices services) {
	return classErroneous.getInstanceFor(instanceSort, services);
    }
    
    
    public Function getLength() {
	return length;
    }    
    
    
    public LocationVariable getSavedHeap() {
        return getAllHeaps().get(1);
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
				          getFieldSort(), 
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
    public final boolean containsFunction(Function op) {
    	if (super.containsFunction(op)) {
    		return true;
    	}
    	if (op instanceof SortDependingFunction) {
    		return ((SortDependingFunction) op).isSimilar(select);
    	}
    	return op.isUnique() && op.sort() == getFieldSort();
    }
    
    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, 
                                 Term[] subs, 
                                 IServices services,
                                 ExecutionContext ec) {
	return false;
    }
    

    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, 
                		 Term left, 
                		 Term right, 
                		 IServices services,
                		 ExecutionContext ec) {
	return false;
    }


    @Override
    public Function getFunctionFor(de.uka.ilkd.key.java.expression.Operator op, 
	    			   IServices serv,
	    			   ExecutionContext ec) {
	assert false;
	return null;
    }

    
    @Override
    public boolean hasLiteralFunction(Function f) {
	return false;
    }

    
    @Override
    public Expression translateTerm(Term t, ExtList children, IServices services) {
    	if (t.op() instanceof SortDependingFunction &&
    			((SortDependingFunction)t.op()).isSimilar(select)) {
    		ProgramVariable heap = (ProgramVariable) children.remove(0);
    		if (heap != getHeap()) {
    			throw new IllegalArgumentException("Can only translate field access to base heap.");
    		}
    		ReferencePrefix prefix = (ReferencePrefix) children.remove(0);
    		ProgramVariable field = (ProgramVariable) children.remove(0);
    		
    		if (prefix instanceof NullLiteral) {
    			return new FieldReference(field, null);
    		}
    		return new FieldReference(field, prefix);
    	} else if (t.sort() == getFieldSort() && t.op() instanceof Function && ((Function) t.op()).isUnique()) {
    		return ((Services)services).getJavaInfo().getAttribute(getPrettyFieldName(t.op()), getClassName((Function) t.op()));
    	}
    	throw new IllegalArgumentException("Could not translate " + ProofSaver.printTerm(t, null) + " to program.");
    }
    

}
