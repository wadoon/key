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

package org.key_project.common.core.logic.op;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.Sort;
import org.key_project.common.core.logic.SpecialSorts;


/**
 * The objects of this class represent logical variables,
 * used e.g. for quantification.
 */
public final class LogicVariable extends DLAbstractSortedOperator 
    implements QuantifiableVariable {

    public LogicVariable(Name name, Sort sort) {
	super(name, null, sort, true);
	assert sort != SpecialSorts.FORMULA;
	assert sort != SpecialSorts.UPDATE;
    }
    
    
    @Override
    public String toString() {
	return name() + ":" + sort();
    }
}