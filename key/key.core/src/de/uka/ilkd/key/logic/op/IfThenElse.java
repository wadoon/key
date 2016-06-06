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

import org.key_project.common.core.logic.Name;

/**
 * This singleton class implements a general conditional operator
 * <tt>\if (phi) \then (t1) \else (t2)</tt>.
 */
public final class IfThenElse extends AbstractOperator {

    public static final IfThenElse IF_THEN_ELSE = new IfThenElse();

    private IfThenElse() {
        super(new Name("if-then-else"), 3, true);
    }
}