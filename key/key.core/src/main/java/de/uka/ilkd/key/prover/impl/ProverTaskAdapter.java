// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.prover.impl;

import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo;

/**
 * Adapter class for {@link ProverTaskListener}.
 * 
 * @author Dominic Steinhoefel
 */
public abstract class ProverTaskAdapter implements ProverTaskListener {

    @Override
    public void taskStarted(TaskStartedInfo info) {
    }

    @Override
    public void taskProgress(int position) {
    }

    @Override
    public void taskFinished(TaskFinishedInfo info) {
    }

}
