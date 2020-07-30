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
 */
public class AbstractExpressionProgramSegment extends AbstractStatementProgramSegment {
    private final String type;

    public AbstractExpressionProgramSegment(final String content, final String apeName,
            final int line, final String type) {
        super(content, apeName, line);
        this.type = type;
    }

    public String getType() {
        return type;
    }

    @Override
    public AbstractExpressionProgramSegment merge(CommentSegment cs) {
        return new AbstractExpressionProgramSegment(cs.getContent() + getContent(), getApeName(),
                getLine(), type);
    }
}
