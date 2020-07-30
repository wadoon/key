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

import java.util.Arrays;
import java.util.List;

import de.uka.ilkd.key.abstractexecution.refinity.util.KeyBridgeUtils;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;

/**
 * @author Dominic Steinhoefel
 */
public class ContinuesSpecProver extends AbstractSpecProver implements InstantiationAspectProver {
    private static final String KEY_PROVE_CONTINUES_SPEC_SCAFFOLD = "/de/uka/ilkd/key/refinity/instantiation/continuesSpecProblem.key";

    private final String keyProveContinuesSpecScaffold;

    public ContinuesSpecProver() {
        super();
        keyProveContinuesSpecScaffold = KeyBridgeUtils.readResource(KEY_PROVE_CONTINUES_SPEC_SCAFFOLD);
    }

    public ContinuesSpecProver(final Profile profile) {
        super(profile);
        keyProveContinuesSpecScaffold = KeyBridgeUtils.readResource(KEY_PROVE_CONTINUES_SPEC_SCAFFOLD);
    }

    @Override
    public String initMessage() {
        return "Proving Continue Behavior Condition(s)...";
    }

    @Override
    public String proofObjective() {
        return "continue behavior condition(s)";
    }

    @Override
    protected List<String> ignPVs() {
        return Arrays.asList(new String[] { "_didContinue" });
    }

    @Override
    protected String keyFileScaffold() {
        return keyProveContinuesSpecScaffold;
    }

    @Override
    protected Behavior targetedBehavior() {
        return Behavior.CONTINUE_BEHAVIOR;
    }

}
