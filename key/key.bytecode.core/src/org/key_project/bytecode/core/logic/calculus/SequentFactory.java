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

package org.key_project.bytecode.core.logic.calculus;

import org.key_project.common.core.logic.calculus.AbstractSequentFactory;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public class SequentFactory extends
        AbstractSequentFactory<Semisequent, Sequent> {

    private static SequentFactory INSTANCE = new SequentFactory();
    
    private SequentFactory() {
        // Private Singleton constructor
    }
    
    public static SequentFactory instance() {
        return INSTANCE;
    }
    
    @Override
    public Sequent createSuccSequent(Semisequent succ) {
        if (succ.isEmpty()) {
            return nil();
        }
        
        return createSequent(SemisequentImpl.nil(), succ);
    }

    @Override
    public Sequent createSequent(Semisequent ante, Semisequent succ) {
        if (ante.isEmpty() && succ.isEmpty()) {
            return nil();
        }
        
        return SequentImpl.createSequent(ante, succ);
    }

    @Override
    public Sequent createAnteSequent(Semisequent ante) {
        if (ante.isEmpty()) {
            return nil();
        }
        
        return createSequent(ante, SemisequentImpl.nil());
    }

    @Override
    public Sequent nil() {
        return SequentImpl.nil();
    }

}
