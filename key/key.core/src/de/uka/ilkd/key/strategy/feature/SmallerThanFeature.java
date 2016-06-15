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

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.LexPathOrdering;
import de.uka.ilkd.key.logic.TermOrdering;


/**
 * Abstract superclass for features comparing terms (in particular polynomials
 * or monomials) using the term ordering
 */
public abstract class SmallerThanFeature extends BinaryTacletAppFeature {

    private final TermOrdering termOrdering = new LexPathOrdering ();

    protected boolean lessThan(JavaDLTerm t1, JavaDLTerm t2, ServiceCaches caches) {
        return compare ( t1, t2 ) < 0;
    }

    protected final int compare(JavaDLTerm t1, JavaDLTerm t2) {
        return termOrdering.compare ( t1, t2 );
    }
    
    /**
     * @param caches TODO
    * @return <code>true</code> iff each element of <code>list1</code> is
     *         strictly smaller than all elements of <code>list2</code>
     */
    protected final boolean lessThan(ImmutableList<JavaDLTerm> list1, ImmutableList<JavaDLTerm> list2, ServiceCaches caches) {
        if ( list2.isEmpty () ) return false;
        for (JavaDLTerm aList1 : list1) {
            final JavaDLTerm te1 = aList1;
            for (JavaDLTerm aList2 : list2) {
                if (!lessThan(te1, aList2, caches)) return false;
            }
        }
        return true;
    }

    protected abstract static class Collector {
    
        private ImmutableList<JavaDLTerm> terms = ImmutableSLList.<JavaDLTerm>nil();
    
        protected void addTerm(JavaDLTerm mon) {
            terms = terms.prepend ( mon );
        }
    
        public ImmutableList<JavaDLTerm> getResult() {
            return terms;
        }
        
    }

}