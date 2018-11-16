// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.lazyse;

import de.uka.ilkd.key.logic.Term;

/**
 * Instantiations for {@link LoopHole}s.
 *
 * @author Dominic Steinhöfel
 */
public class LoopHoleInstantiation {
    private final LoopHole loopHole;
    private final Term pathCondInst;
    private final Term symbStoreInst;

    public LoopHoleInstantiation(LoopHole loopHole, Term pathCondInst,
            Term symbStoreInst) {
        this.loopHole = loopHole;
        this.pathCondInst = pathCondInst;
        this.symbStoreInst = symbStoreInst;
    }

    public LoopHole getLoopHole() {
        return loopHole;
    }

    public Term getPathCondInst() {
        return pathCondInst;
    }

    public Term getSymbStoreInst() {
        return symbStoreInst;
    }
}