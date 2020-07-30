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
package de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.proginst;

/**
 * @author Dominic Steinhoefel
 *
 */
public class AbstractStatementProgramSegment extends ProgramSegment {
    private final String apeName;
    private final int line;

    public AbstractStatementProgramSegment(final String content, final String apeName, final int line) {
        super(content);
        this.apeName = apeName;
        this.line = line;
    }

    public String getApeName() {
        return apeName;
    }

    public int getLine() {
        return line;
    }

    public AbstractStatementProgramSegment merge(final CommentSegment cs) {
        return new AbstractStatementProgramSegment(cs.getContent() + getContent(), apeName, line);
    }
}
