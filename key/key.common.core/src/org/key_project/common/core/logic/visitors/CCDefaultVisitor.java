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

package org.key_project.common.core.logic.visitors;

import org.key_project.common.core.logic.CCTerm;

/**
 * This abstract Vistor class declares the interface for a common term visitor.
 *
 * @author Dominic Scheurer
 */
public abstract class CCDefaultVisitor<T extends CCTerm<?, ?, T>> implements CCTermVisitor<T> {

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.CCVisitor#visitSubtree(org.key_project.common.core.logic.CCTerm)
     */
    @Override
    public boolean visitSubtree(T visited) {
        // TODO Auto-generated method stub
        return false;
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.CCVisitor#subtreeEntered(org.key_project.common.core.logic.CCTerm)
     */
    @Override
    public void subtreeEntered(T subtreeRoot) {
        // TODO Auto-generated method stub
        
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.CCVisitor#subtreeLeft(org.key_project.common.core.logic.CCTerm)
     */
    @Override
    public void subtreeLeft(T subtreeRoot) {
        // TODO Auto-generated method stub
        
    }

}
