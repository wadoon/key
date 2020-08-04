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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.antlr.runtime.RecognitionException;

import de.uka.ilkd.key.abstractexecution.refinity.instantiation.exception.InvalidSyntaxException;
import de.uka.ilkd.key.abstractexecution.refinity.instantiation.exception.TriviallySatisfiedSpecCaseException;
import de.uka.ilkd.key.abstractexecution.refinity.instantiation.resultobjects.CompletionCondition;
import de.uka.ilkd.key.abstractexecution.refinity.instantiation.resultobjects.ProofResult;
import de.uka.ilkd.key.abstractexecution.refinity.instantiation.resultobjects.RetrieveProgramResult;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.APEInstantiation;
import de.uka.ilkd.key.abstractexecution.refinity.util.KeyBridgeUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;

/**
 * Abstract super class for provers of abrupt completion behavior.
 * 
 * @author Dominic Steinhoefel
 */
public abstract class AbstractSpecProver implements InstantiationAspectProver {
    private static final String FUNCTIONS = "<FUNCTIONS>";
    private static final String PREDICATES = "<PREDICATES>";
    private static final String PROGRAMVARIABLES = "<PROGRAMVARIABLES>";

    private static final String PRECONDITION = "<PRECONDITION>";
    private static final String ADDITIONAL_PREMISES = "<ADDITIONAL_PREMISES>";
    private static final String SYMINSTS = "<SYMINSTS>";
    private static final String PARAMS = "<PARAMS>";

    private static final String PRE_SPEC = "<PRE_SPEC>";
    private static final String POST_SPEC = "<POST_SPEC>";

    private final InstantiationAspectProverHelper helper;

    private static String mquote(final String str) {
        return Matcher.quoteReplacement(str);
    }

    private static String pquote(final String str) {
        return Pattern.quote(str);
    }

    public AbstractSpecProver(final InstantiationAspectProverHelper helper) {
        this.helper = helper;
    }

    public AbstractSpecProver() {
        helper = new InstantiationAspectProverHelper(new JavaProfile());
    }

    @Override
    public ProofResult prove(AEInstantiationModel model) {
        return model.getApeInstantiations().stream().map(inst -> proveAbrComplSpecInst(model, inst))
                .collect(ProofResult.REDUCER);
    }

    private String createProveAbrComplBehSpecKeYFile(final AEInstantiationModel model,
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

            final List<String> ignPVs = new ArrayList<>(ignPVs());
            Arrays.stream(new String[] { "_objUnderTest", "heap", "savedHeap" })
                    .forEach(ignPVs::add);

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
                    .stream().filter(cond -> cond.getBehavior() == targetedBehavior()).findAny()
                    .orElseThrow(() -> new TriviallySatisfiedSpecCaseException());

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

        return keyFileScaffold()
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
     * @return The behavior targeted of the specification case (e.g., completion due
     * to a break).
     */
    protected abstract Behavior targetedBehavior();

    /**
     * @return The content of the KeY problem file scaffold.
     */
    protected abstract String keyFileScaffold();

    /**
     * @return The lists of program variables to ignore (not declare as new
     * variables).
     */
    protected abstract List<String> ignPVs();

    /**
     * @return Some Java code which should be added after the instantiation. For
     * instance, a break statement if return behavior should be checked: thus, it is
     * made sure that no wrong result is produced due to the default "return null;"
     * in the Java scaffold.
     */
    protected String javaCodeSuffix() {
        return "";
    }

    /**
     * Attempts to prove that the given instantiation satisfies the frame condition
     * of the APE to instantiate.
     * 
     * @param inst The {@link APEInstantiation}
     * @return A {@link ProofResult} for the frame problem.
     */
    private ProofResult proveAbrComplSpecInst(final AEInstantiationModel model,
            APEInstantiation inst) {
        String keyFileContent;
        try {
            keyFileContent = createProveAbrComplBehSpecKeYFile(model, inst);
        } catch (TriviallySatisfiedSpecCaseException e) {
            return ProofResult.EMPTY;
        }

        final String javaFileContent = helper.createJavaFile(model,
                inst.getInstantiation() + javaCodeSuffix());

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

}
