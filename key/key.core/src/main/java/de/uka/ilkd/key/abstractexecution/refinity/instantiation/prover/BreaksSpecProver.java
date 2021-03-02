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
package de.uka.ilkd.key.abstractexecution.refinity.instantiation.prover;

import java.util.Arrays;
import java.util.List;

import de.uka.ilkd.key.abstractexecution.refinity.util.KeyBridgeUtils;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;

/**
 * @author Dominic Steinhoefel
 */
public class BreaksSpecProver extends AbstractSpecProver implements InstantiationAspectProver {
    private static final String KEY_PROVE_BREAKS_SPEC_SCAFFOLD = "/de/uka/ilkd/key/refinity/instantiation/breaksSpecProblem.key";

    private final String keyProveBreaksSpecScaffold;

    public BreaksSpecProver() {
        super();
        keyProveBreaksSpecScaffold = KeyBridgeUtils.readResource(KEY_PROVE_BREAKS_SPEC_SCAFFOLD);
    }

    public BreaksSpecProver(final InstantiationAspectProverHelper helper) {
        super(helper);
        keyProveBreaksSpecScaffold = KeyBridgeUtils.readResource(KEY_PROVE_BREAKS_SPEC_SCAFFOLD);
    }

    @Override
    public String initMessage() {
        return "Proving Break Behavior Condition(s)...";
    }

    @Override
    public String proofObjective() {
        return "break behavior condition(s)";
    }

    @Override
    protected List<String> ignPVs() {
        return Arrays.asList(new String[] { "_didBreak" });
    }

    @Override
    protected String keyFileScaffold() {
        return keyProveBreaksSpecScaffold;
    }

    @Override
    protected Behavior targetedBehavior() {
        return Behavior.BREAK_BEHAVIOR;
    }

}
