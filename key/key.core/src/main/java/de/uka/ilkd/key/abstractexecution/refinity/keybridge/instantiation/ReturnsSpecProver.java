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

import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.antlr.runtime.RecognitionException;

import de.uka.ilkd.key.abstractexecution.refinity.keybridge.CompletionCondition;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.InvalidSyntaxException;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.ProofResult;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.RetrieveProgramResult;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.TriviallySatisfiedSpecCaseException;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.APEInstantiation;
import de.uka.ilkd.key.abstractexecution.refinity.util.KeyBridgeUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;

/**
 * @author Dominic Steinhoefel
 *
 */
public class ReturnsSpecProver implements InstantiationAspectProver {
    private static final String RETURNS_SPEC_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/refinity/instantiation/returnsSpecProblem.key";

    private static final String FUNCTIONS = "<FUNCTIONS>";
    private static final String PREDICATES = "<PREDICATES>";
    private static final String PROGRAMVARIABLES = "<PROGRAMVARIABLES>";

    private static final String PRECONDITION = "<PRECONDITION>";
    private static final String ADDITIONAL_PREMISES = "<ADDITIONAL_PREMISES>";
    private static final String SYMINSTS = "<SYMINSTS>";
    private static final String PARAMS = "<PARAMS>";

    private static final String PRE_SPEC = "<PRE_SPEC>";
    private static final String POST_SPEC = "<POST_SPEC>";

    private final InstantiationAspectProverHelper helper = InstantiationAspectProverHelper.INSTANCE;

    private final String keyProveReturnsSpecScaffold;

    private static String mquote(final String str) {
        return Matcher.quoteReplacement(str);
    }

    private static String pquote(final String str) {
        return Pattern.quote(str);
    }

    public ReturnsSpecProver() {
        keyProveReturnsSpecScaffold = KeyBridgeUtils
                .readResource(RETURNS_SPEC_PROBLEM_FILE_SCAFFOLD);
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
    public ProofResult prove(AEInstantiationModel model) {
        return model.getApeInstantiations().stream().map(inst -> proveReturnSpecInst(model, inst))
                .collect(ProofResult.REDUCER);
    }

    private String createProveReturnSpecKeYFile(final AEInstantiationModel model,
            final APEInstantiation inst) throws TriviallySatisfiedSpecCaseException {
        final RetrieveProgramResult retrProgRes = helper.retrieveProgram(model,
                inst.getInstantiation());

        final Services services = retrProgRes.getServices();

        final String javaDLPreCondRelation = KeyBridgeUtils.createJavaDLPreCondition(
                model.getPreCondition(), model.getProgramVariableDeclarations(),
                model.getAbstractLocationSets(), model.getPredicateDeclarations(),
                model.getFunctionDeclarations(), KeyBridgeUtils.dummyKJT(), services);

        //////////

        final String symInsts = InstantiationAspectProverHelper.createLocSetInstAssumptions(model);

        //////////

        final String newVars;

        {
            final ProgramVariableCollector progVarCol = new ProgramVariableCollector(
                    retrProgRes.getProgram(), retrProgRes.getLocalSpecRepo(),
                    retrProgRes.getServices());
            progVarCol.start();

            final List<String> ignPVs = Arrays.asList(
                    new String[] { "result", "_returned", "_objUnderTest", "heap", "savedHeap" });

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

        final String prespec;
        final String postspec;

        {
            final CompletionCondition condition = helper.getCompletionConditions(model, inst)
                    .stream().filter(cond -> cond.getBehavior() == Behavior.RETURN_BEHAVIOR)
                    .findAny().orElseThrow(() -> new TriviallySatisfiedSpecCaseException());

            try {
                prespec = helper.instantiate( //
                        condition.getJavaDLPrecondition().orElse("true"), model, services);
                postspec = helper.instantiate( //
                        condition.getJavaDLPostcondition().orElse("true"), model, services);
            } catch (RecognitionException e) {
                throw new InvalidSyntaxException(
                        "Could not parse precondition, postcondition, or their instantiations: "
                                + e.getMessage(),
                        e);
            }

        }

        return keyProveReturnsSpecScaffold
                .replaceAll(FUNCTIONS,
                        mquote(InstantiationAspectProverHelper.createFuncDecls(model)))
                .replaceAll(PREDICATES,
                        mquote(InstantiationAspectProverHelper.createPredDecls(model)))
                .replaceAll(PROGRAMVARIABLES,
                        mquote(InstantiationAspectProverHelper.createProgvarDecls(model) + newVars))
                .replaceAll(PARAMS, mquote(InstantiationAspectProverHelper.createParams(model)))
                .replaceAll(SYMINSTS, Matcher.quoteReplacement(symInsts))
                .replaceAll(pquote(PRECONDITION), mquote(javaDLPreCondRelation))
                .replaceAll(ADDITIONAL_PREMISES,
                        mquote(KeyBridgeUtils
                                .createAdditionalPremises(model.getAbstractLocationSets())))
                .replaceAll(PRE_SPEC, mquote(prespec)) //
                .replaceAll(POST_SPEC, mquote(postspec));
    }

    /**
     * Attempts to prove that the given instantiation satisfies the frame condition
     * of the APE to instantiate.
     * 
     * @param inst The {@link APEInstantiation}
     * @return A {@link ProofResult} for the frame problem.
     */
    private ProofResult proveReturnSpecInst(final AEInstantiationModel model,
            APEInstantiation inst) {
        String keyFileContent;
        try {
            keyFileContent = createProveReturnSpecKeYFile(model, inst);
        } catch (TriviallySatisfiedSpecCaseException e) {
            return ProofResult.EMPTY;
        }

        final String javaFileContent = helper.createJavaFile(model, inst.getInstantiation());

        final Proof proof;
        try {
            proof = KeyBridgeUtils.createProofAndRun(keyFileContent, javaFileContent, 10000);
        } catch (RuntimeException rte) {
            // Maybe convert to different exception class...
            throw rte;
        }

        return new ProofResult(proof.closed(), proof,
                KeyBridgeUtils.getFilenameForAPEProof(proofObjective(), proof.closed(), inst));
    }

}
