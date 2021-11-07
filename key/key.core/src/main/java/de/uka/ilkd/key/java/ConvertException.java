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

package de.uka.ilkd.key.java;

/**
 * This exception class is mainly thrown by Recoder2KeY and its companions.
 * <p>
 * It stores its reason not only by the cause mechanism of Exceptions but also
 * separately if it is a parser error.
 * <p>
 * This information is then read by the KeYParser to produce helpful error
 * messages.
 */
public class ConvertException extends RuntimeException {

    /**
     *
     */
    private static final long serialVersionUID = 7112945712992241455L;

    public ConvertException(String errmsg) {
        super(errmsg);
    }

    public ConvertException(Throwable pe) {
        super(pe);
    }

    public ConvertException(String errmsg, Throwable cause) {
        super(errmsg, cause);
    }
}