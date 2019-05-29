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

package de.uka.ilkd.key.logic.label;

import de.uka.ilkd.key.abstractexecution.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;

/**
 * Label attached to Skolem updates arising from abstract execution. An update
 * U_sk generated for an abstract program P is labeled <code>&lt;&lt;P>></code>.
 * Using this label, a possibly existing block contract for P can be looked up,
 * especially its assignable(_not) clauses, such that updates can be simplified
 * more effectively.
 */
public class AbstractExecutionTermLabel implements TermLabel {
    /**
     * The unique name of this label.
     */
    public static final Name NAME = new Name("AE");

    /**
     * The name used in {@link Services#getCounter(String)} to keep track of the
     * already used IDs.
     */
    public static final String PROOF_COUNTER_NAME = "AE_LABEL_COUNTER";

    /**
     * The abstract program contained in this label.
     */
    private final AbstractPlaceholderStatement abstrPlaceholderStmt;

    /**
     * Constructor.
     *
     * @param id
     *            The abstract program contained in this label.
     */
    public AbstractExecutionTermLabel(
            AbstractPlaceholderStatement abstrPlaceholderStmt) {
        this.abstrPlaceholderStmt = abstrPlaceholderStmt;
    }

    @Override
    public boolean equals(Object o) {
        return o instanceof AbstractExecutionTermLabel
                && ((AbstractExecutionTermLabel) o).abstrPlaceholderStmt
                        .equals(abstrPlaceholderStmt);
    }

    @Override
    public int hashCode() {
        return abstrPlaceholderStmt.hashCode();
    }

    @Override
    public String toString() {
        return NAME.toString() + "(" + getAbstrPlaceholderStmt() + ")";
    }

    @Override
    public Object getChild(int i) {
        switch (i) {
        case 0:
            return getAbstrPlaceholderStmt();
        default:
            return null;
        }
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    /**
     * @return The abstract program contained in this label.
     */
    public AbstractPlaceholderStatement getAbstrPlaceholderStmt() {
        return abstrPlaceholderStmt;
    }

    @Override
    public Name name() {
        return NAME;
    }
}