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

package org.key_project.bytecode.core.logic.op;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.program.CCSourceElement;
import org.key_project.common.core.program.NameAbstractionTable;
import org.key_project.common.core.program.abstraction.SortedType;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public class ProgramConstant extends ProgramVariable {
    
    /**
     * TODO: Document.
     *
     * @param name
     * @param s
     * @param t
     * @param isModel
     * @param isGhost
     */
    protected ProgramConstant(Name name, SortedType t, boolean isStatic) {
        super(name, t.getSort(), t, false, false, false, isStatic);
    }

    @Override
    public boolean equalsModRenaming(CCSourceElement se,
            NameAbstractionTable<CCSourceElement> nat) {
        return nat.sameAbstractName(this, se);
    }

    @Override
    public Operator rename(Name name) {
        return new ProgramConstant(name, getType(), isStatic());
    }
    
}
