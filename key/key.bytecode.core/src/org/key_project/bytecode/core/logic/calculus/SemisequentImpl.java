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

import org.key_project.bytecode.core.logic.Term;
import org.key_project.common.core.logic.calculus.CCSemisequentChangeInfo;
import org.key_project.common.core.logic.calculus.CCSemisequentImpl;
import org.key_project.common.core.logic.calculus.SequentFormula;
import org.key_project.util.collection.ImmutableList;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public class SemisequentImpl extends CCSemisequentImpl<Term, Semisequent>
        implements Semisequent {
    
    private static final Semisequent EMPTY = new SemisequentImpl();
    
    public SemisequentImpl() {
        super();
    }
    
    /**
     * TODO: Document.
     *
     * @param modifiedFormulas
     */
    public SemisequentImpl(ImmutableList<SequentFormula<Term>> modifiedFormulas) {
        super(modifiedFormulas);
    }
    
    public static Semisequent nil() {
        return EMPTY;
    }

    @Override
    protected CCSemisequentChangeInfo<Term, Semisequent> createSemisequentChangeInfo(
            ImmutableList<org.key_project.common.core.logic.calculus.SequentFormula<Term>> formulas) {
        return new SemisequentChangeInfo(formulas);
    }

}
