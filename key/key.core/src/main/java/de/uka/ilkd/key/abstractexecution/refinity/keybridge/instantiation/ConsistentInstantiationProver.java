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
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.init.Profile;

/**
 * Proves that all APEs with the same identifiers are instantiated consistently,
 * i.e., the instantiated programs are equivalent modulo renaming of their
 * footprint.
 * 
 * <p>CURRENTLY NOT IMPLEMENTED.
 * 
 * <p>Implementation strategy: Create renaming table based on comparing frames and
 * footprints, then check equalsModRenaming of {@link SourceElement}. The
 * problematic case are partial instantiations with abstract elements, then this
 * cannot as easily be done.
 * 
 * @author Dominic Steinhoefel
 */
public class ConsistentInstantiationProver implements InstantiationAspectProver {
    public ConsistentInstantiationProver() {
    }

    public ConsistentInstantiationProver(final Profile profile) {
    }

    @Override
    public ProofResult prove(final AEInstantiationModel model) {
        return ProofResult.EMPTY;
    }

    @Override
    public String initMessage() {
        return "[NOT YET IMPLEMENTED] Proving " + proofObjective() + "...";
    }

    @Override
    public String proofObjective() {
        return "consistent instantiation of APEs";
    }

}
