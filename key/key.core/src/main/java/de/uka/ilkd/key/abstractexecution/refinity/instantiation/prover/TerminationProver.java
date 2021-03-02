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

import de.uka.ilkd.key.abstractexecution.refinity.instantiation.resultobjects.ProofResult;
import de.uka.ilkd.key.abstractexecution.refinity.instantiation.resultobjects.RetrieveProgramResult;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.APEInstantiation;
import de.uka.ilkd.key.abstractexecution.refinity.util.KeyBridgeUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Proof;

/**
 * @author Dominic Steinhoefel
 *
 */
public class TerminationProver implements InstantiationAspectProver {
    private static final String TERMINATION_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/refinity/instantiation/terminationProblem.key";

    private static final String PRECONDITION = "<PRECONDITION>";
    private static final String PROGRAMVARIABLES = "<PROGRAMVARIABLES>";
    private static final String PREDICATES = "<PREDICATES>";
    private static final String FUNCTIONS = "<FUNCTIONS>";
    private static final String PARAMS = "<PARAMS>";
    private static final String ADDITIONAL_PREMISES = "<ADDITIONAL_PREMISES>";
    private static final String SYMINSTS = "<SYMINSTS>";

    private final InstantiationAspectProverHelper helper;

    private final String keyProveTerminationScaffold;

    public TerminationProver() {
        keyProveTerminationScaffold = KeyBridgeUtils
                .readResource(TERMINATION_PROBLEM_FILE_SCAFFOLD);
        helper = new InstantiationAspectProverHelper();
    }

    public TerminationProver(final InstantiationAspectProverHelper helper) {
        keyProveTerminationScaffold = KeyBridgeUtils
                .readResource(TERMINATION_PROBLEM_FILE_SCAFFOLD);
        this.helper = helper;
    }

    @Override
    public ProofResult prove(AEInstantiationModel model) {
        return model.getApeInstantiations().stream().map(inst -> proveTermination(model, inst))
                .collect(ProofResult.REDUCER);
    }

    @Override
    public String initMessage() {
        return "Proving Termination (if applicable)...";
    }

    @Override
    public String proofObjective() {
        return "termination";
    }

    /**
     * Attempts to prove that the given instantiation satisfies the frame condition
     * of the APE to instantiate.
     * 
     * @param inst The {@link APEInstantiation}
     * @return A {@link ProofResult} for the frame problem.
     */
    private ProofResult proveTermination(final AEInstantiationModel model, APEInstantiation inst) {
        final String keyFileContent = createProveTerminationKeYFile(model, inst);
        final String javaFileContent = helper.createJavaFile(model, inst.getInstantiation());

        final Proof proof;
        try {
            proof = KeyBridgeUtils.createProofAndRun(keyFileContent, javaFileContent, 10000,
                    helper.profile());
        } catch (RuntimeException rte) {
            // Maybe convert to different exception class...
            throw rte;
        }

        return new ProofResult(proof.closed(), proof,
                KeyBridgeUtils.getFilenameForAPEProof(proofObjective(), proof.closed(), inst));
    }

    private String createProveTerminationKeYFile(final AEInstantiationModel model,
            final APEInstantiation inst) {
        // TODO: Termination only has to be proven if the APE is specified to terminate.
        // This information has to be added to the model!

        final Services services = helper.getPopulatedDummyServices(model);

        final String javaDLPreCondRelation = KeyBridgeUtils.createJavaDLPreCondition(
                model.getPreCondition(), model.getProgramVariableDeclarations(),
                model.getAbstractLocationSets(), model.getPredicateDeclarations(),
                model.getFunctionDeclarations(), KeyBridgeUtils.dummyKJT(), services);

        //////////

        final String symInsts = InstantiationAspectProverHelper.createLocSetInstAssumptions(model);

        //////////

        final String newVars;

        {
            final RetrieveProgramResult retrProgRes = helper.retrieveProgram(model,
                    inst.getInstantiation());
            final ProgramVariableCollector progVarCol = new ProgramVariableCollector(
                    retrProgRes.getProgram(), retrProgRes.getLocalSpecRepo(),
                    retrProgRes.getServices());
            progVarCol.start();

            final List<String> ignPVs = Arrays
                    .asList(new String[] { "_result", "_exc", "_objUnderTest" });

            final LinkedHashSet<LocationVariable> instProgVars = progVarCol.result().stream()
                    .filter(lv -> !ignPVs.contains(lv.name().toString()))
                    .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));

            final String newInstVars = instProgVars.stream()
                    .filter(lv -> !model.getProgramVariableDeclarations().stream()
                            .anyMatch(pvd -> pvd.getName().equals(lv.name().toString())))
                    .map(lv -> String.format("%s %s;",
                            lv.getKeYJavaType().getSort().name().toString(), lv.name().toString()))
                    .collect(Collectors.joining("\n  "));

            newVars = "\n  " + newInstVars;
        }

        return keyProveTerminationScaffold
                .replaceAll(FUNCTIONS,
                        Matcher.quoteReplacement(
                                InstantiationAspectProverHelper.createFuncDecls(model)))
                .replaceAll(PREDICATES,
                        Matcher.quoteReplacement(
                                InstantiationAspectProverHelper.createPredDecls(model)))
                .replaceAll(PROGRAMVARIABLES, Matcher.quoteReplacement(
                        InstantiationAspectProverHelper.createProgvarDecls(model) + newVars))
                .replaceAll(PARAMS,
                        Matcher.quoteReplacement(
                                InstantiationAspectProverHelper.createParams(model)))
                .replaceAll(SYMINSTS, Matcher.quoteReplacement(symInsts))
                .replaceAll(Pattern.quote(PRECONDITION),
                        Matcher.quoteReplacement(javaDLPreCondRelation))
                .replaceAll(ADDITIONAL_PREMISES, Matcher.quoteReplacement(
                        KeyBridgeUtils.createAdditionalPremises(model.getAbstractLocationSets())));
    }

}
