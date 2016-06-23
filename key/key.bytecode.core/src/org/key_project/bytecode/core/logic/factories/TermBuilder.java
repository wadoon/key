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

package org.key_project.bytecode.core.logic.factories;

import org.key_project.bytecode.core.logic.InstructionBlock;
import org.key_project.bytecode.core.logic.Term;
import org.key_project.bytecode.core.logic.op.WarySubstOp;
import org.key_project.bytecode.core.logic.services.BCTermServices;
import org.key_project.common.core.logic.factories.CCTermBuilderImpl;
import org.key_project.common.core.logic.factories.CCTermFactoryImpl;
import org.key_project.common.core.logic.op.CCSubstOp;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public class TermBuilder extends CCTermBuilderImpl<InstructionBlock, Term> {

    /**
     * TODO: Document.
     *
     * @param tf
     * @param services
     */
    public TermBuilder(CCTermFactoryImpl<InstructionBlock, Term> tf,
            BCTermServices services) {
        super(tf, services);
    }

    @Override
    protected CCSubstOp<InstructionBlock, Term> substOp() {
        return WarySubstOp.SUBST;
    }

}
