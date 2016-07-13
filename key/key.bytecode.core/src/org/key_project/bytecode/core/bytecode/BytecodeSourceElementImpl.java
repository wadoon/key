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

package org.key_project.bytecode.core.bytecode;

import org.key_project.common.core.program.NameAbstractionTable;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public class BytecodeSourceElementImpl implements
        BytecodeSourceElement {

    @Override
    public void visit(BytecodeVisitor v) {
     // XXX implement
        throw new UnsupportedOperationException("Method not yet implemented");
    }

    @Override
    public boolean equalsModRenaming(BytecodeSourceElement se,
            NameAbstractionTable<BytecodeSourceElement> nat) {
        // XXX implement
        throw new UnsupportedOperationException("Method not yet implemented");
    }

}
