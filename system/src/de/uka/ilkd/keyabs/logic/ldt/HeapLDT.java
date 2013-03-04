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

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.ldt.AbstractHeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.LocationVariable;


/**
 * LDT responsible for the "Heap" sort, and the associated "Field" sort. Besides
 * offering the usual LDT functionality, this class is also responsible for
 * creating and managing the constant symbols representing fields. 
 */
public final class HeapLDT extends AbstractHeapLDT {
    
    public static final Name NAME = new Name("Heap");    
        
    private static final Name[] VALID_HEAP_NAMES = { BASE_HEAP_NAME };


    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    public HeapLDT(IServices services) {
	    super(NAME, services);
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
    

    @Override
    public Name[] getAllHeapNames() {
	return VALID_HEAP_NAMES;
    }
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    

    
}
