// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.refinity.model;

import java.util.List;

/**
 * @author Dominic Steinhoefel
 */
public interface FuncOrPredDecl {
    String getName();
    
    boolean isFuncDecl();
    
    default boolean isPredDecl() {
        return !isFuncDecl();
    }
    
    List<String> getArgSorts();
    
    default FunctionDeclaration toFuncDecl() {
        assert isFuncDecl();
        return (FunctionDeclaration) this;
    }
    
    default PredicateDeclaration toPredDecl() {
        assert isPredDecl();
        return (PredicateDeclaration) this;
    }
    
}
