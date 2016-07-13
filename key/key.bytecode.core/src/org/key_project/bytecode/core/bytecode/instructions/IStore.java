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

package org.key_project.bytecode.core.bytecode.instructions;

import org.key_project.bytecode.core.bytecode.operands.ProgVarOperand;
import org.key_project.common.core.logic.Name;
import org.key_project.util.collection.ImmutableList;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public class IStore extends UnaryInstruction<ProgVarOperand> {

    private static final Name NAME = new Name("ISTORE");

    /**
     * TODO: Document.
     *
     * @param operand
     */
    public IStore(ProgVarOperand operand) {
        super(operand);
    }
    
    /**
     * TODO: Document.
     *
     * @param operands
     */
    public IStore(ImmutableList<ProgVarOperand> operands) {
        super(operands);
    }

    @Override
    public Name name() {
        return NAME;
    }

}
