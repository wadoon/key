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

package de.uka.ilkd.key.strategy.termgenerator;

import java.util.Iterator;

import org.key_project.common.core.logic.calculus.SequentFormula;

import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * JavaDLTerm generator that enumerates the formulas of the current
 * sequent/antecedent/succedent.
 */
public abstract class SequentFormulasGenerator implements TermGenerator {

    protected SequentFormulasGenerator() {}
    
    public static SequentFormulasGenerator antecedent() {
        return new SequentFormulasGenerator () {
            protected Iterator<SequentFormula<JavaDLTerm>> generateForIt(Goal goal) {
                return goal.sequent ().antecedent ().iterator ();
            }
        };
    }
    
    public static SequentFormulasGenerator succedent() {
        return new SequentFormulasGenerator () {
            protected Iterator<SequentFormula<JavaDLTerm>> generateForIt(Goal goal) {
                return goal.sequent ().succedent ().iterator ();
            }
        };
    }
    
    public static SequentFormulasGenerator sequent() {
        return new SequentFormulasGenerator () {
            protected Iterator<SequentFormula<JavaDLTerm>> generateForIt(Goal goal) {
                return goal.sequent ().iterator ();
            }
        };
    }
    
    protected abstract Iterator<SequentFormula<JavaDLTerm>> generateForIt(Goal goal);

    public Iterator<JavaDLTerm> generate(RuleApp app, PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> pos, Goal goal) {
        return new SFIterator ( generateForIt ( goal ) );
    }

    private static class SFIterator implements Iterator<JavaDLTerm> {
        private final Iterator<SequentFormula<JavaDLTerm>> forIt;

        public boolean hasNext() {
            return forIt.hasNext ();
        }

        public JavaDLTerm next() {
            return forIt.next ().formula ();
        }

        public SFIterator(Iterator<SequentFormula<JavaDLTerm>> forIt) {
            this.forIt = forIt;
        }
        
        /** 
         * throw an unsupported operation exception
         */
        public void remove() {
            throw new UnsupportedOperationException();
        }
        
    }
}