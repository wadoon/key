// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2020 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation;

import de.uka.ilkd.key.abstractexecution.refinity.keybridge.ProofResult;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;

/**
 * One particular aspect of the correctness of the instantiation of an abstract
 * program model.
 * 
 * @author Dominic Steinhoefel
 */
public interface InstantiationAspectProver {

    /**
     * Prove the represented aspect of the model.
     * 
     * @param model The model to consider.
     * @return A {@link ProofResult}.
     */
    ProofResult prove(AEInstantiationModel model);
    
    String initMessage();
    
    String proofObjective();
}
