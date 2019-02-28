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

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;

/**
 * A Skolem location set suitable for use in an {@link AbstractUpdate}.
 *
 * @author Dominic Steinhoefel
 */
public class SkolemLoc implements AbstrUpdateLHS, AbstrUpdateRHS {
    private final Function skLoc;

    public SkolemLoc(Function skLoc) {
        this.skLoc = skLoc;
    }

    @Override
    public Term toRHSTerm(Services services) {
        return services.getTermBuilder().func(skLoc);
    }

    @Override
    public Term toLHSTerm(Services services) {
        return toRHSTerm(services);
    }
}
