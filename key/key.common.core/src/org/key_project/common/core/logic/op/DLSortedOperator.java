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

import org.key_project.common.core.logic.DLOperator;
import org.key_project.common.core.logic.DLSort;
import org.key_project.common.core.logic.DLTerm;
import org.key_project.common.core.logic.DLVisitor;
import org.key_project.util.collection.ImmutableArray;


/** 
 * Operator with well-defined argument and result sorts.
 */
public interface DLSortedOperator<S extends DLSort, T extends DLTerm<S, ? extends DLVisitor<T>>> extends DLOperator<S, T> {
    
    S sort();

    S argSort(int i);
    
    public ImmutableArray<? extends S> argSorts();
}