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

package org.key_project.common.core.logic;

/**
 * This abstract Vistor class declares the interface for a common term visitor.
 */
public abstract class DefaultVisitor<T extends DLTerm<? extends DLVisitor<T>>> implements DLVisitor<T> {	
    @Override
    public boolean visitSubtree(T visited) {
        return true;
    }

    @Override
    public void subtreeEntered(T subtreeRoot){
    }

    @Override
    public void subtreeLeft(T subtreeRoot){
    }    
}