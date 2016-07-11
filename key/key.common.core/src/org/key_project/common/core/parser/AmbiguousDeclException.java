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

package org.key_project.common.core.parser;

@SuppressWarnings("serial")
public class AmbiguousDeclException extends KeYSemanticException {

    public AmbiguousDeclException(String fileName, int line, int charPositionInLine, String ambigious_symbol) {
        super(fileName, getMessage(ambigious_symbol), line, charPositionInLine);
    }

    public static String getMessage(String ambigious_symbol) {
        return "The name \'" + ambigious_symbol + "\' is already in use.";
    }

}