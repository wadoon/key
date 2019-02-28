// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.logic.op.locs;

import java.util.Map;

import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SortedOperator;

/**
 * A left-hand side or right-hand side location of an abstract update.
 *
 * @author Dominic Steinhoefel
 */
public interface AbstractUpdateLoc extends SortedOperator {
    /**
     * Returns a new {@link AbstractUpdateLoc} of this one with the
     * {@link ProgramVariable}s replaced according to the supplied map.
     *
     * @param replMap
     *            The replace map.
     * @return A new {@link AbstractUpdateLoc} of this one with the
     *         {@link ProgramVariable}s replaced according to the supplied map.
     */
    AbstractUpdateLoc replaceVariables(
            Map<ProgramVariable, ProgramVariable> replMap);

    /**
     * All {@link AbstractUpdateLoc}s are containers. This method returns the
     * "real" KeY {@link Operator} which they represent.
     *
     * @return The KeY {@link Operator} that this {@link AbstractUpdateLoc}
     *         container represents.
     */
    Operator childOp();
}
