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

import org.antlr.v4.runtime.Token;
import org.key_project.common.core.logic.sort.Sort;

public class GenericSortException extends RuntimeException {
    private static final long serialVersionUID = 9202076114305420730L;
    
    private String cat;
    private String filename;
    private Sort sort;
    private String reason;
    private int line;
    private int charPositionInLine;

    public GenericSortException(String cat, String reason,
            Sort sort, Token t, String filename) {
        this.cat = cat;
        this.reason = reason;
        this.filename = filename;
        this.sort = sort;
        this.line = t.getLine();
        this.charPositionInLine = t.getCharPositionInLine();
    }

    public GenericSortException(String cat, String reason, Sort sort,
            String filename, int line, int column) {
        this.cat = cat;
        this.reason = reason;
        this.filename = filename;
        this.sort = sort;
        this.line = line;
        this.charPositionInLine = column;
    }

    /**
     * Returns a clean error message (no line number/column information)
     */
    public String getMessage() {
        String errmsg = cat + "\n  " + sort + "\n";
        return errmsg + reason;
    }

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
        return filename + "(" + this.line + ", " + this.charPositionInLine + "): "
                + getMessage();
    }
}