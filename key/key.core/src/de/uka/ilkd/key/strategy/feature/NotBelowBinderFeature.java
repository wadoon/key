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

package de.uka.ilkd.key.strategy.feature;

import org.key_project.common.core.logic.calculus.PIOPathIterator;
import org.key_project.common.core.logic.calculus.PosInOccurrence;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.Debug;


/**
 * Returns zero iff the position of a rule application is not below any
 * operators that bind variables
 */
public class NotBelowBinderFeature extends BinaryFeature {

    public static final Feature INSTANCE = new NotBelowBinderFeature ();

    private NotBelowBinderFeature () {}
    
    public boolean filter (RuleApp<Term, Goal> app, PosInOccurrence<Term> pos, Goal goal) {
        Debug.assertFalse ( pos == null,
                            "Feature is only applicable to rules with find" );

        return !belowBinder ( pos );
    }

    private boolean belowBinder (PosInOccurrence<Term> pos) {
        final PIOPathIterator<Term> it = pos.iterator ();

        while ( it.next () != -1 ) {
            final Term t = it.getSubTerm ();

            if ( t.varsBoundHere ( it.getChild () ).size () > 0 ) return true;
        }
        
        return false;
    }

}