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
 * Simple class encapsulating a pair of an update and a term label.
 */
public class UpdateLabelPair<T extends CCTerm<?, ?, ?, T>> {
    private T update;
    private ImmutableArray<TermLabel> updateApplicationlabels;

    public UpdateLabelPair(T update,
            ImmutableArray<TermLabel> updateApplicationlabels) {
        this.update = update;
        this.updateApplicationlabels = updateApplicationlabels;
    }

    public T getUpdate() {
        return update;
    }

    public ImmutableArray<TermLabel> getUpdateApplicationlabels() {
        return updateApplicationlabels;
    }

    @Override
    public int hashCode() {
        return update.hashCode() +
                updateApplicationlabels.hashCode() * 7;
    }

    @SuppressWarnings("unchecked")
    @Override
    public boolean equals(Object obj) {
        if (obj instanceof UpdateLabelPair) {
            return update.equals(((UpdateLabelPair<T>) obj).getUpdate())
                    &&
                    updateApplicationlabels.equals(((UpdateLabelPair<T>) obj)
                            .getUpdateApplicationlabels());
        }
        else {
            return false;
        }
    }
}