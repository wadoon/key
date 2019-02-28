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
import de.uka.ilkd.key.logic.Term;

/**
 * A has-to location for use in an abstract update.
 *
 * @author Dominic Steinhoefel
 */
public class HasToLoc implements AbstrUpdateLHS {
    private final AbstrUpdateLHS child;

    public HasToLoc(AbstrUpdateLHS child) {
        assert !(child instanceof HasToLoc);
        assert !(child instanceof AllLocsLoc);
        this.child = child;
    }

    @Override
    public Term toLHSTerm(Services services) {
        return services.getTermBuilder().hasTo(child.toLHSTerm(services));
    }
}
