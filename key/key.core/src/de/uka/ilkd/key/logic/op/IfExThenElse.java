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
 * This singleton class implements a conditional operator "\ifEx iv; (phi) \then
 * (t1) \else (t2)", where iv is an integer logic variable, phi is a formula,
 * and where t1 and t2 are terms with the same sort. The variable iv is bound in
 * phi and in t1, but not in t2.
 */
public final class IfExThenElse extends AbstractOperator {

    public static final IfExThenElse IF_EX_THEN_ELSE = new IfExThenElse();

    private IfExThenElse() {
        super(new Name("ifExThenElse"), 3, new Boolean[] { true, true, false },
                true);
    }
}