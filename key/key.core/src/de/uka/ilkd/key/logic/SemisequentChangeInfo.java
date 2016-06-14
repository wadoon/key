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

import org.key_project.common.core.logic.calculus.SequentFormula;
import org.key_project.util.collection.ImmutableList;

/**
 * Records the changes made to a semisequent. Keeps track of added and
 * removed formula to the semisequents. 
 */
public class SemisequentChangeInfo extends GenericSemisequentChangeInfo<SequentFormula<JavaDLTerm>, Semisequent> {
   
    public SemisequentChangeInfo(ImmutableList<SequentFormula<JavaDLTerm>> formulas) {
        super(formulas);
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.GenericSemisequentChangeInfo#createSemisequent(org.key_project.util.collection.ImmutableList)
     */
    @Override
    protected GenericSemisequent<SequentFormula<JavaDLTerm>> createSemisequent(
            ImmutableList<SequentFormula<JavaDLTerm>> modifiedFormulas) {
        return new Semisequent(modifiedFormulas);
    }
}