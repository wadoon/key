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

package org.key_project.common.core.logic;

import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * Collects all operators occurring in the traversed term.
 */
public class DLOpCollector<O extends Operator, T extends DLTerm<? extends DLVisitor<T>>> extends DefaultVisitor<T> {
    
    /** the found operators */
    protected final HashSet<O> ops;

    /** creates the Op collector */
    public DLOpCollector() {
        ops = new LinkedHashSet<O>();
    }

    @SuppressWarnings("unchecked")
    public void visit(T t) {           
        ops.add((O)t.op());
    }

    public boolean contains(O op) {
    return ops.contains(op);
    }
    
    public Set<O> ops() {
    return ops;
    }
}