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
import org.key_project.common.core.program.Position;
import org.key_project.common.core.program.PositionInfo;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public class BytecodeSourceElementImpl implements
        BytecodeSourceElement {

    @Override
    public BytecodeSourceElementImpl getFirstElement() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public BytecodeSourceElementImpl getFirstElementIncludingBlocks() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public BytecodeSourceElementImpl getLastElement() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Position getStartPosition() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Position getEndPosition() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Position getRelativePosition() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public PositionInfo getPositionInfo() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public void visit(BytecodeVisitor v) {
        // TODO Auto-generated method stub

    }

    @Override
    public boolean equalsModRenaming(BytecodeSourceElement se,
            NameAbstractionTable<BytecodeSourceElement> nat) {
        // TODO Auto-generated method stub
        return false;
    }

}
