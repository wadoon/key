// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.recoderext;

import recoder.java.Expression;
import recoder.java.ExpressionContainer;
import recoder.java.NamedProgramElement;
import recoder.java.reference.MethodReference;
import recoder.java.reference.ReferenceSuffix;
import recoder.java.reference.TypeReference;
import recoder.java.reference.TypeReferenceContainer;

/**
 * A shortcut-statement for a method body with direct embedding, i.e., without
 * adding a method frame. Used for constructions with exec statements for
 * Abstract Execution.
 */
public class DirectMethodBodyStatement extends MethodBodyStatement implements
        TypeReferenceContainer, ExpressionContainer, NamedProgramElement, ReferenceSuffix {
    private static final long serialVersionUID = 1L;

    public DirectMethodBodyStatement(TypeReference bodySource, Expression resultVar,
            MethodReference methRef) {
        super(bodySource, resultVar, methRef);
    }

}