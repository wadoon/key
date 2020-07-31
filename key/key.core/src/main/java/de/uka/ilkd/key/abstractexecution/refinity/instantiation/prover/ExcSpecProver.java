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
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;

/**
 * @author Dominic Steinhoefel
 *
 */
public class ExcSpecProver extends AbstractSpecProver implements InstantiationAspectProver {
    private static final String EXC_SPEC_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/refinity/instantiation/excSpecProblem.key";

    private final String keyProveExcSpecScaffold;

    public ExcSpecProver() {
        super();
        keyProveExcSpecScaffold = KeyBridgeUtils.readResource(EXC_SPEC_PROBLEM_FILE_SCAFFOLD);
    }

    public ExcSpecProver(final Profile profile) {
        super(profile);
        keyProveExcSpecScaffold = KeyBridgeUtils.readResource(EXC_SPEC_PROBLEM_FILE_SCAFFOLD);
    }

    @Override
    public String initMessage() {
        return "Proving Exceptional Behavior Condition(s)...";
    }

    @Override
    public String proofObjective() {
        return "exceptional behavior condition(s)";
    }

    @Override
    protected List<String> ignPVs() {
        return Arrays.asList(new String[] { "result", "_returned" });
    }

    @Override
    protected String keyFileScaffold() {
        return keyProveExcSpecScaffold;
    }

    @Override
    protected Behavior targetedBehavior() {
        return Behavior.EXCEPTIONAL_BEHAVIOR;
    }

}
