// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.op;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Operator with well-defined argument and result sorts.<br/>
 * 
 * <strong>TODO:</strong> This should be named "SortedOperator"; the previous
 * {@link SortedOperator} interface should get a different name.
 *
 * @author Dominic Scheurer
 */
public interface GenericSortedOperator extends GenericOperator {

    Sort sort();

    Sort argSort(int i);

    ImmutableArray<Sort> argSorts();

}