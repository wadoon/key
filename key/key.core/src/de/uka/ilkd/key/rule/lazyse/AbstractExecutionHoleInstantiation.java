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
 * Instantiations for {@link AbstractExecutionHole}s.
 *
 * @author Dominic Steinhöfel
 */
public class AbstractExecutionHoleInstantiation {
    private final AbstractExecutionHole loopHole;
    private final Term pathCondInst;
    private final Term symbStoreInst;

    public AbstractExecutionHoleInstantiation(AbstractExecutionHole loopHole,
            Term pathCondInst, Term symbStoreInst) {
        this.loopHole = loopHole;
        this.pathCondInst = pathCondInst;
        this.symbStoreInst = symbStoreInst;
    }

    public AbstractExecutionHole getLoopHole() {
        return loopHole;
    }

    public Term getPathCondInst() {
        return pathCondInst;
    }

    public Term getSymbStoreInst() {
        return symbStoreInst;
    }
}