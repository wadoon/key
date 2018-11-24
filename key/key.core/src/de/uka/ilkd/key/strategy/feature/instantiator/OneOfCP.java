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

package de.uka.ilkd.key.strategy.feature.instantiator;

import java.util.Iterator;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.feature.Feature;
import de.uka.ilkd.key.strategy.feature.MutableState;

public class OneOfCP implements Feature {
    
    private final Feature features[];

    private int theChosenOne;
    private final ChoicePoint cp = new CP ();
    
    private OneOfCP(Feature[] features) {
        this.features = features;
    }

    public static Feature create(Feature[] features) {
        return new OneOfCP ( features );
    }
    
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mState) {        
        final BackTrackingManager manager = mState.getBacktrackingManager();
        manager.passChoicePoint ( cp, this );
        return features[theChosenOne].computeCost ( app, pos, goal, mState );
    }
    
    private final class CP implements ChoicePoint {
        private final class BranchIterator implements Iterator<CPBranch> {
            private int num = 0;
            private final RuleApp oldApp;
            
            public BranchIterator(RuleApp oldApp) {
                this.oldApp = oldApp;
            }

            public boolean hasNext () {
                return num < features.length;
            }

            public CPBranch next() {
                final int chosen = num++;
                return new CPBranch () {
                    public void choose () {
                        theChosenOne = chosen;
                    }
                    public RuleApp getRuleAppForBranch () {
                        return oldApp;
                    }
                };
            }
            
            /** 
             * throws an unsupported operation exception
             */
            public void remove() {
                throw new UnsupportedOperationException();
            }
        }
            
        public Iterator<CPBranch> getBranches(RuleApp oldApp) {
            return new BranchIterator ( oldApp );
        }
    }
}