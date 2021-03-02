// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2020 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.refinity.instantiation.exception;

/**
 * Thrown if a specification case is trivially satisfied, e.g., because no
 * return pre- and postcondition is specified.
 * 
 * @author Dominic Steinhoefel
 */
public class TriviallySatisfiedSpecCaseException extends Exception {
    private static final long serialVersionUID = 1L;

    public TriviallySatisfiedSpecCaseException() {
        super("Specification case is trivially satisfied.");
    }

    /**
     * @param message
     */
    public TriviallySatisfiedSpecCaseException(String message) {
        super(message);
    }

    /**
     * @param cause
     */
    public TriviallySatisfiedSpecCaseException(Throwable cause) {
        super(cause);
    }

    /**
     * @param message
     * @param cause
     */
    public TriviallySatisfiedSpecCaseException(String message, Throwable cause) {
        super(message, cause);
    }

}
