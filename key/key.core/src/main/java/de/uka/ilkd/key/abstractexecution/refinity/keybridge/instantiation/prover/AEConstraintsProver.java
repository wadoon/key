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
package de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.prover;

import org.antlr.runtime.RecognitionException;

import de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.proginst.AbstractProgramInstantiator;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.resultobjects.ProofResult;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;
import de.uka.ilkd.key.proof.init.Profile;

/**
 * Proves that specified <tt>ae_constraint</tt>s are satisfied.
 * 
 * NOT YET IMPLEMENTED.
 * 
 * @author Dominic Steinhoefel
 */
public class AEConstraintsProver implements InstantiationAspectProver {
    private final InstantiationAspectProverHelper helper;

    public AEConstraintsProver() {
        helper = new InstantiationAspectProverHelper();
    }

    public AEConstraintsProver(final Profile profile) {
        helper = new InstantiationAspectProverHelper(profile);
    }

    @Override
    public ProofResult prove(final AEInstantiationModel model) {
        final AbstractProgramInstantiator instantiator = new AbstractProgramInstantiator(model, helper);
        try {
            final String instProg = instantiator.instantiate();
        } catch (RecognitionException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        return ProofResult.EMPTY;
    }

    @Override
    public String initMessage() {
        return "[NOT YET IMPLEMENTED] Proving " + proofObjective() + "...";
    }

    @Override
    public String proofObjective() {
        return "validity of instantiated assumptions";
    }

}
