// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package org.key_project.common.core.logic;

import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.util.collection.ImmutableArray;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 */
public interface LabeledTerm {

    /**
     * {@inheritDoc}
     */
    boolean hasLabels();

    /**
     * returns the labels attached to this term
     */
    ImmutableArray<TermLabel> getLabels();

    TermLabel getLabel(Name termLabelName);

    /**
     * returns true if the given label is attached
     * 
     * @param label
     *            the TermLabel for which to look (must not be null)
     * @return true iff. the label is attached to this term
     */
    boolean containsLabel(TermLabel label);

    /**
     * {@inheritDoc}
     */
    boolean equals(Object o);

    /**
     * {@inheritDoc}
     */
    int computeHashCode();

    /**
     * {@inheritDoc}
     */
    String toString();

}