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
package de.uka.ilkd.key.java.recoderext;

import recoder.java.ProgramElement;

/**
 * {@link AbstractProgramElement}s are the core of <em>Abstract Execution</em>.
 * So far, {@link AbstractStatement}s and {@link AbstractExpression}s are
 * implemented.
 *
 * @author Dominic Steinhoefel
 */
public interface AbstractProgramElement extends ProgramElement {
    String getId();
    void setId(String id);
}