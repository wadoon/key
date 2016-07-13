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

package org.key_project.common.core.parser.exceptions;

@SuppressWarnings("serial")
public class KeYSemanticException extends RuntimeException {
    private final String cat;
    private final String filename;
    private final int line;
    private final int charPositionInLine;

    public KeYSemanticException(String fileName, String message, int line, int charPositionInLine) {
        super(message);
        this.cat = message;
        this.filename = fileName;
        this.line = line;
        this.charPositionInLine = charPositionInLine;
    }

    public KeYSemanticException(String fileName, String message, int line, int charPositionInLine, Exception cause) {
        super(message, cause);
        this.cat = message;
        this.filename = fileName;
        this.line = line;
        this.charPositionInLine = charPositionInLine;
    }

    public String getFilename() {
        return filename;
    }

    public int getLine() {
        return line;
    }

    public int getColumn() {
        return charPositionInLine;
    }

    /**
     * Returns a clean error message (no line number/column information)
     * 
     * @deprecated
     */
    @Deprecated
    public String getErrorMessage() {
        return getMessage();
    }

    /**
     * Returns a clean error message (no line number/column information)
     */
    public String getMessage() {
        return cat;
    }

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
        return filename + "(" + this.getLine() + ", " + this.getColumn() + "): "
                + getMessage();
    }
}