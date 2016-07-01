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

package de.uka.ilkd.key.logic;

import org.key_project.common.core.logic.calculus.CCSemisequentChangeInfo;
import org.key_project.common.core.logic.calculus.CCSemisequentImpl;
import org.key_project.common.core.logic.calculus.SequentFormula;
import org.key_project.util.collection.ImmutableList;

/**
 * This class represents the succedent or antecendent part of a sequent. It is
 * more or less a list without duplicates and subsumed formulas. This is ensured
 * using method removeRedundancy. In future versions it can be enhanced to do
 * other simplifications. A sequent and so a semisequent has to be immutable.
 */
public class Semisequent extends
        CCSemisequentImpl<Term, Semisequent> {

    private static final Semisequent EMPTY = new Semisequent();

    /**
     * TODO: Document.
     *
     * @param seqList
     */
    Semisequent(ImmutableList<SequentFormula<Term>> seqList) {
        super(seqList);
    }

    /**
     * TODO: Document.
     *
     * @param seqList
     */
    public Semisequent(SequentFormula<Term> seqList) {
        super(seqList);
    }

    /**
     * TODO: Document.
     *
     */
    public Semisequent() {
        super();
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.key.logic.GenericSemisequent#createSemisequentChangeInfo(
     * org.key_project.util.collection.ImmutableList)
     */
    @Override
    protected CCSemisequentChangeInfo<Term, Semisequent> createSemisequentChangeInfo(
            ImmutableList<SequentFormula<Term>> formulas) {
        return new SemisequentChangeInfo(formulas);
    }

    public static Semisequent nil() {
        return EMPTY;
    }
}
