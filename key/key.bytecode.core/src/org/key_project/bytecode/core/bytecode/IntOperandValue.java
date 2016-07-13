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

import org.key_project.bytecode.core.bytecode.abstraction.PrimitiveType;
import org.key_project.bytecode.core.bytecode.abstraction.Type;
import org.key_project.bytecode.core.services.TheoryServices;
import org.key_project.common.core.theories.CCTheory;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 */
public class IntOperandValue implements OperandValue {
    
    final int val;

    /**
     * TODO: Document.
     *
     * @param i
     */
    public IntOperandValue(int val) {
        this.val = val;
    }

    @Override
    public Type type() {
        return PrimitiveType.JAVA_INT;
    }

    @Override
    public CCTheory theory(TheoryServices services) {
        return services.getIntegerTheory();
    }

}
