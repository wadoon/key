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

import org.key_project.common.core.logic.GenericTerm;
import org.key_project.common.core.logic.calculus.SequentFormula;

/**
 * This interface represents an iterator, iterating the nodes on the
 * path between the root of a term and a position within the term,
 * given by a <code>PosInOccurrence</code>-object
 */
public interface PIOPathIterator<T extends GenericTerm<?,?,?,T>, SeqFor extends SequentFormula<?, ?, ?, T>> extends IntIterator {

    /**
     * @return the number of the next child on the path, or
     * <code>-1</code> if no further child exists
     */
    int         next               ();

    // The following methods may only be called after having called
    // <code>next()</code> at least once

    /**
     * @return the current position within the term
     * (i.e. corresponding to the latest <code>next()</code>-call)
     */
    PosInOccurrence<T,SeqFor> getPosInOccurrence ();

    /**
     * @return the current subterm this object points to
     * (i.e. corresponding to the latest <code>next()</code>-call);
     * this method satisfies
     * <code>getPosInOccurrence().subTerm()==getSubTerm()</code>
     */
    T            getSubTerm         ();

    /**
     * @return the number of the next child on the path, or
     * <code>-1</code> if no further child exists (this is the number
     * that was also returned by the last call of <code>next()</code>)
     */
    int             getChild           ();

}