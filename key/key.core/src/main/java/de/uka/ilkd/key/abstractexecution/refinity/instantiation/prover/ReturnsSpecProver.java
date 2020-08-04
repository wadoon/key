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
public class ReturnsSpecProver extends AbstractSpecProver implements InstantiationAspectProver {
    private static final String KEY_PROVE_RETURNS_SPEC_SCAFFOLD = "/de/uka/ilkd/key/refinity/instantiation/returnsSpecProblem.key";

    private final String keyProveReturnsSpecScaffold;

    public ReturnsSpecProver() {
        super();
        keyProveReturnsSpecScaffold = KeyBridgeUtils.readResource(KEY_PROVE_RETURNS_SPEC_SCAFFOLD);
    }

    public ReturnsSpecProver(final InstantiationAspectProverHelper helper) {
        super(helper);
        keyProveReturnsSpecScaffold = KeyBridgeUtils.readResource(KEY_PROVE_RETURNS_SPEC_SCAFFOLD);
    }

    @Override
    public String initMessage() {
        return "Proving Return Behavior Condition(s)...";
    }

    @Override
    public String proofObjective() {
        return "return behavior condition(s)";
    }

    @Override
    protected List<String> ignPVs() {
        return Arrays.asList(new String[] { "result", "_returned" });
    }

    @Override
    protected String keyFileScaffold() {
        return keyProveReturnsSpecScaffold;
    }

    @Override
    protected Behavior targetedBehavior() {
        return Behavior.RETURN_BEHAVIOR;
    }
    
    @Override
    protected String javaCodeSuffix() {
        return "\nbreak;";
    }

}
