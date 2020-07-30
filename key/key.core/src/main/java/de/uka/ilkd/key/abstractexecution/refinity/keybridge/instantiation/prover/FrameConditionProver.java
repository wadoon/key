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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.exception.UnsuccessfulAPERetrievalException;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.resultobjects.ProofResult;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.resultobjects.RetrieveProgramResult;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.APEInstantiation;
import de.uka.ilkd.key.abstractexecution.refinity.util.KeyBridgeUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;

/**
 * @author Dominic Steinhoefel
 *
 */
public class FrameConditionProver implements InstantiationAspectProver {
    private static final String FRAME_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/refinity/instantiation/frameProblem.key";

    private static final String PRECONDITION = "<PRECONDITION>";
    private static final String PROGRAMVARIABLES = "<PROGRAMVARIABLES>";
    private static final String PREDICATES = "<PREDICATES>";
    private static final String FUNCTIONS = "<FUNCTIONS>";
    private static final String PARAMS = "<PARAMS>";
    private static final String ADDITIONAL_PREMISES = "<ADDITIONAL_PREMISES>";
    private static final String SYMINSTS = "<SYMINSTS>";
    private static final String ASSIGNABLES = "<ASSIGNABLES>";
    private static final String AT_PRES = "<AT_PRES>";
    private static final String PV_AT_PRE_POSTS = "<PV_AT_PRE_POSTS>";

    private final InstantiationAspectProverHelper helper;

    private final String keyProveFrameScaffold;

    public FrameConditionProver() {
        keyProveFrameScaffold = KeyBridgeUtils.readResource(FRAME_PROBLEM_FILE_SCAFFOLD);
        helper = new InstantiationAspectProverHelper();
    }

    public FrameConditionProver(final Profile profile) {
        keyProveFrameScaffold = KeyBridgeUtils.readResource(FRAME_PROBLEM_FILE_SCAFFOLD);
        helper = new InstantiationAspectProverHelper(profile);
    }

    @Override
    public ProofResult prove(AEInstantiationModel model) {
        return model.getApeInstantiations().stream().map(inst -> proveFrameInst(model, inst))
                .collect(ProofResult.REDUCER);
    }

    @Override
    public String initMessage() {
        return "Proving Frame Condition(s)...";
    }

    @Override
    public String proofObjective() {
        return "frame condition(s)";
    }

    /**
     * Attempts to prove that the given instantiation satisfies the frame condition
     * of the APE to instantiate.
     * 
     * @param inst The {@link APEInstantiation}
     * @return A {@link ProofResult} for the frame problem.
     */
    private ProofResult proveFrameInst(final AEInstantiationModel model, APEInstantiation inst) {
        final String keyFileContent = createProveFrameKeYFile(model, inst);
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

    private String createProveFrameKeYFile(final AEInstantiationModel model,
            final APEInstantiation inst) {
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

        final String atPres;
        final LinkedHashSet<LocationVariable> instProgVars;

        {
            final ProgramVariableCollector progVarCol = new ProgramVariableCollector(
                    retrProgRes.getProgram(), retrProgRes.getLocalSpecRepo(), services);
            progVarCol.start();

            final List<String> ignPVs = Arrays
                    .asList(new String[] { "_result", "_exc", "_objUnderTest" });

            instProgVars = progVarCol.result().stream()
                    .filter(lv -> !ignPVs.contains(lv.name().toString()))
                    .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
            atPres = instProgVars.stream().map(pv -> String.format("%1$s_AtPre:=%1$s", pv))
                    .collect(Collectors.joining("||"));
        }

        //////////

        final String javaDlAssignableTerm = getAssignableTermString(model, inst, services);

        //////////

        final String pvAtPrePosts;

        {
            pvAtPrePosts = instProgVars.stream().filter(
                    lv -> lv.sort() != services.getTypeConverter().getHeapLDT().targetSort())
                    .map(LocationVariable::toString)
                    .map(v -> String.format("(%1$s=%1$s_AtPre | pvElementOf(PV(%1$s), %2$s))", v,
                            javaDlAssignableTerm))
                    .collect(Collectors.joining("\n              & "));
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

        return keyProveFrameScaffold
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
                .replaceAll(AT_PRES, Matcher.quoteReplacement(atPres))
                .replaceAll(ASSIGNABLES, Matcher.quoteReplacement(javaDlAssignableTerm))
                .replaceAll(PV_AT_PRE_POSTS, pvAtPrePosts)
                .replaceAll(Pattern.quote(PRECONDITION),
                        Matcher.quoteReplacement(javaDLPreCondRelation))
                .replaceAll(ADDITIONAL_PREMISES, Matcher.quoteReplacement(
                        KeyBridgeUtils.createAdditionalPremises(model.getAbstractLocationSets())));
    }

    /**
     * Returns a String representation of the assignable term of the given
     * {@link APEInstantiation}.
     * 
     * @param inst
     * @return
     * @throws UnsuccessfulAPERetrievalException
     */
    private String getAssignableTermString(final AEInstantiationModel model,
            final APEInstantiation inst, final Services services)
            throws UnsuccessfulAPERetrievalException {
        return LogicPrinter.quickPrintTerm(helper.getJMLAssignableTerm(model, inst, services),
                services, false, false);
    }

}
