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

import org.key_project.common.core.logic.calculus.CCSemisequentChangeInfo;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public class SemisequentChangeInfo extends
        CCSemisequentChangeInfo<SequentFormula, Semisequent> {

    /**
     * TODO: Document.
     *
     */
    public SemisequentChangeInfo() {
        super(ImmutableSLList.<SequentFormula> nil());
    }
    
    /**
     * TODO: Document.
     *
     * @param formulas
     */
    public SemisequentChangeInfo(ImmutableList<SequentFormula> formulas) {
        super(formulas);
    }

    @Override
    protected Semisequent createSemisequent(
            ImmutableList<SequentFormula> modifiedFormulas) {
        if (modifiedFormulas.isEmpty()) {
            return SemisequentImpl.nil();
        }
        
        return new SemisequentImpl(modifiedFormulas);
    }

}
