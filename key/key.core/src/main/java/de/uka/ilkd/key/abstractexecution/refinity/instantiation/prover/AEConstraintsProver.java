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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.antlr.runtime.RecognitionException;

import de.uka.ilkd.key.abstractexecution.refinity.instantiation.exception.InvalidSyntaxException;
import de.uka.ilkd.key.abstractexecution.refinity.instantiation.proginst.AbstractProgramInstantiator;
import de.uka.ilkd.key.abstractexecution.refinity.instantiation.resultobjects.ProofResult;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;
import de.uka.ilkd.key.abstractexecution.refinity.util.KeyBridgeUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;

/**
 * Proves that specified <tt>ae_constraint</tt>s are satisfied.
 * 
 * NOT YET IMPLEMENTED.
 * 
 * @author Dominic Steinhoefel
 */
public class AEConstraintsProver implements InstantiationAspectProver {
    private static final String CONSTRAINTS_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/refinity/instantiation/constraintsProblem.key";

    private final InstantiationAspectProverHelper helper;

    private final String keyProveConstraintsScaffold;

    private static final String PRECONDITION = "<PRECONDITION>";
    private static final String PROGRAMVARIABLES = "<PROGRAMVARIABLES>";
    private static final String PREDICATES = "<PREDICATES>";
    private static final String FUNCTIONS = "<FUNCTIONS>";
    private static final String PARAMS = "<PARAMS>";
    private static final String ADDITIONAL_PREMISES = "<ADDITIONAL_PREMISES>";

    public AEConstraintsProver() {
        helper = new InstantiationAspectProverHelper();
        keyProveConstraintsScaffold = KeyBridgeUtils
                .readResource(CONSTRAINTS_PROBLEM_FILE_SCAFFOLD);
    }

    public AEConstraintsProver(final Profile profile) {
        helper = new InstantiationAspectProverHelper(profile);
        keyProveConstraintsScaffold = KeyBridgeUtils
                .readResource(CONSTRAINTS_PROBLEM_FILE_SCAFFOLD);
    }

    @Override
    public ProofResult prove(final AEInstantiationModel model) {
        final AbstractProgramInstantiator instantiator = //
                new AbstractProgramInstantiator(model, helper);
        try {
            final String instProg = instantiator.instantiate();

            if (!instantiator.hasAEConstraints()) {
                // no ae_constraints to prove
                return ProofResult.EMPTY;
            }

            final String keyFileContent = createProveConstraintsKeYFile(model,
                    instantiator.getServices());
            final String javaFileContent = helper.createJavaFile(model, instProg);

            final Proof proof = KeyBridgeUtils.createProofAndRun(keyFileContent, javaFileContent,
                    10000, helper.profile());

            return new ProofResult(proof.closed(), proof,
                    KeyBridgeUtils.getFilenameForProof(proofObjective(), proof.closed()));

        } catch (RecognitionException e) {
            throw new InvalidSyntaxException(
                    "Problems parsing proof file for constraint checking: %s", e);
        }
    }

    @Override
    public String initMessage() {
        return "Proving " + proofObjective() + "...";
    }

    @Override
    public String proofObjective() {
        return "validity of instantiated assumptions";
    }

    private String createProveConstraintsKeYFile(final AEInstantiationModel model,
            final Services services) {
        final String javaDLPreCondRelation = KeyBridgeUtils.createJavaDLPreCondition(
                model.getPreCondition(), model.getProgramVariableDeclarations(),
                model.getAbstractLocationSets(), model.getPredicateDeclarations(),
                model.getFunctionDeclarations(), KeyBridgeUtils.dummyKJT(), services);

        //////////

        final LinkedHashSet<LocationVariable> instProgVars;

        {
            final List<String> ignPVs = Arrays
                    .asList(new String[] { "_result", "_exc", "_objUnderTest" });

            instProgVars = services.getNamespaces().programVariables().allElements().stream()
                    .filter(LocationVariable.class::isInstance).map(LocationVariable.class::cast)
                    .filter(lv -> !ignPVs.contains(lv.name().toString()))
                    .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
        }

        //////////

        final String newVars;

        {
            final String newInstVars = instProgVars.stream()
                    .filter(lv -> !model.getProgramVariableDeclarations().stream()
                            .anyMatch(pvd -> pvd.getName().equals(lv.name().toString())))
                    .map(lv -> String.format("%s %s;",
                            lv.getKeYJavaType().getSort().name().toString(), lv.name().toString()))
                    .collect(Collectors.joining("\n  "));

            final String atPreVars = instProgVars.stream()
                    .map(lv -> String.format("%s %s_AtPre;",
                            lv.getKeYJavaType().getSort().name().toString(), lv.name().toString()))
                    .collect(Collectors.joining("\n  "));

            newVars = "\n  " + newInstVars + "\n  " + atPreVars;
        }

        return keyProveConstraintsScaffold
                .replaceAll(FUNCTIONS,
                        Matcher.quoteReplacement(
                                InstantiationAspectProverHelper.createFuncDecls(model)))
                .replaceAll(PREDICATES,
                        Matcher.quoteReplacement(
                                InstantiationAspectProverHelper.createPredDecls(model)))
                .replaceAll(PROGRAMVARIABLES, Matcher.quoteReplacement(
                        InstantiationAspectProverHelper.createProgvarDecls(model) + newVars))
                .replaceAll(ADDITIONAL_PREMISES,
                        Matcher.quoteReplacement(KeyBridgeUtils
                                .createAdditionalPremises(model.getAbstractLocationSets())))
                .replaceAll(Pattern.quote(PRECONDITION),
                        Matcher.quoteReplacement(javaDLPreCondRelation))
                .replaceAll(PARAMS, Matcher
                        .quoteReplacement(InstantiationAspectProverHelper.createParams(model)));
    }

}
