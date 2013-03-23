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

package de.uka.ilkd.key.java;


import java.util.HashMap;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;



public class KeYRecoderMapping extends AbstractKeYProgramModelMapping {

    /** a pseudo super class for all arrays used to declare length */
    private KeYJavaType superArrayType=null;

    public KeYRecoderMapping() {
    	super();
    }

    /**
    * creates a KeYRecoderMapping object.
    * Used for cloning and testing.
    * @param map a HashMap mapping ProgramElements in Recoder to
    * ProgramElements in KeY
    * @param revMap the reverse map (KeY->Recoder)
    * @param parsedSpecial boolean indicating if the special classes have been parsed in
    */
    KeYRecoderMapping(HashMap map, HashMap revMap,
                             KeYJavaType superArrayType,
			     boolean parsedSpecial){
    	super(map, revMap, parsedSpecial);
    	this.superArrayType = superArrayType;
    }

    public void setSuperArrayType(KeYJavaType superArrayType) {
        this.superArrayType = superArrayType;
    }

    public KeYJavaType getSuperArrayType() {
        return this.superArrayType;
    }

    @Override
	public KeYRecoderMapping copy() {
	return new KeYRecoderMapping((HashMap)map.clone(), 
				     (HashMap)revMap.clone(),
                                     superArrayType,
				     parsedSpecial);
    }

}
