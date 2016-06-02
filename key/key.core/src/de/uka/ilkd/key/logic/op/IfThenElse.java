// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.op;

import org.key_project.common.core.logic.*;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.sort.NullSort;


/**
 * This singleton class implements a general conditional operator 
 * <tt>\if (phi) \then (t1) \else (t2)</tt>.
 */
public final class IfThenElse extends AbstractOperator implements Operator {
    
    public static final IfThenElse IF_THEN_ELSE = new IfThenElse();
    
        
    private IfThenElse () {
        super(new Name("if-then-else"), 3, true);
    }
    
    
    private org.key_project.common.core.logic.Sort getCommonSuperSort(org.key_project.common.core.logic.Sort s1, org.key_project.common.core.logic.Sort s2, TermServices services) {
        if(s1 == SpecialSorts.FORMULA) {
            assert s2 == SpecialSorts.FORMULA: "Sorts FORMULA and "+s2+" are incompatible.";
            return SpecialSorts.FORMULA;
        } else if(s1.extendsTrans(s2, services)) {
            return s2;
        } else if(s2.extendsTrans(s1, services)) {
            return s1;
        } else if(s1 instanceof NullSort || s2 instanceof NullSort) {
            return SpecialSorts.ANY;
        } else {
            org.key_project.common.core.logic.Sort result = SpecialSorts.ANY;
            final ImmutableSet<Sort> set1 = services.getDirectSuperSorts(s1);
            final ImmutableSet<Sort> set2 = services.getDirectSuperSorts(s2);
            assert set1 != null : "null for sort: " + s1;
            assert set2 != null : "null for sort: " + s2;
            
            for(final Sort sort1 : set1) {
                if(set2.contains(sort1)) {
                    if(result == SpecialSorts.ANY) {
                        result = sort1;
                    } else {
                        // not uniquely determinable
                        return SpecialSorts.ANY;
                    }
                } 
            }
            
            return result;
        }
    }        

    
  
}