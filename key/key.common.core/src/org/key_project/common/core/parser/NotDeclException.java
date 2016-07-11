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
public class NotDeclException extends KeYSemanticException {

    public NotDeclException(String fileName, int line, int charPositionInLine, String category, String undeclared_symbol) {
        super(fileName, getMessage(category, undeclared_symbol), line, charPositionInLine);
    }

    /**
     * Returns a clean error message (no line number/column information)
     */
    private static String getMessage(String cat, String undeclaredSymbol) {
        return cat + "\n\t" + undeclaredSymbol + "\n" + "not declared";
    }

}