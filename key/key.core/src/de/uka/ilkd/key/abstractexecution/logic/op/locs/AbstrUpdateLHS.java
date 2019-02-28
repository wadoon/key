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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.SetLDT;
import de.uka.ilkd.key.logic.Term;

/**
 * A left-hand side of an abstract update.
 *
 * @author Dominic Steinhoefel
 */
public interface AbstrUpdateLHS extends AbstractUpdateLoc {
    /**
     * @param services
     *            The {@link Services} object.
     * @return A {@link Term} of {@link SetLDT} type suitable as a left-hand
     *         side of an abstract update (but not yet wrapped in a setSingleton
     *         or the like).
     */
    Term toLHSTerm(Services services);
}
