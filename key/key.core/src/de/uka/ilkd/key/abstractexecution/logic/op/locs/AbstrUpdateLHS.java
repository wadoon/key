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

/**
 * A left-hand side of an abstract update.
 *
 * @author Dominic Steinhoefel
 */
public interface AbstrUpdateLHS extends AbstractUpdateLoc {
    /**
     * @return This {@link AbstrUpdateLHS} as an {@link AbstrUpdateUpdatableLoc}
     *         (RHS). Principle use case is to unwrap hasTo-s.
     */
    AbstrUpdateUpdatableLoc toUpdatableRHS();
}
