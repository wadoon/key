// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2020 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.refinity.keybridge;

public class UnsuccessfulAPERetrievalException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    private final static String MESSAGE_PREFIX = "Could not retrieve APEs from program";
    private final static String MESSAGE_SEP = ", message: ";

    public UnsuccessfulAPERetrievalException() {
        super(MESSAGE_PREFIX);
    }

    public UnsuccessfulAPERetrievalException(String message, Throwable cause,
            boolean enableSuppression, boolean writableStackTrace) {
        super(MESSAGE_PREFIX + MESSAGE_SEP + message, cause, enableSuppression,
                writableStackTrace);
    }

    public UnsuccessfulAPERetrievalException(String message, Throwable cause) {
        super(MESSAGE_PREFIX + MESSAGE_SEP + message, cause);
    }

    public UnsuccessfulAPERetrievalException(String message) {
        super(MESSAGE_PREFIX + MESSAGE_SEP + message);
    }

    public UnsuccessfulAPERetrievalException(Throwable cause) {
        super(MESSAGE_PREFIX, cause);
    }
}