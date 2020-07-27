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
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.antlr.runtime.RecognitionException;

import de.uka.ilkd.key.abstractexecution.refinity.keybridge.InvalidSyntaxException;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.ProofResult;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.RetrieveProgramResult;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.APEInstantiation;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.FunctionInstantiation;
import de.uka.ilkd.key.abstractexecution.refinity.util.KeyBridgeUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;

/**
 * @author Dominic Steinhoefel
 *
 */
public class FootprintConditionProver implements InstantiationAspectProver {
    private static final String FOOTPRINT_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/refinity/instantiation/footprintProblem.key";

    private static final String FUNCTIONS = "<FUNCTIONS>";
    private static final String PREDICATES = "<PREDICATES>";
    private static final String PROGRAMVARIABLES = "<PROGRAMVARIABLES>";

    private static final String PRECONDITION = "<PRECONDITION>";
    private static final String ADDITIONAL_PREMISES = "<ADDITIONAL_PREMISES>";
    private static final String SYMINSTS = "<SYMINSTS>";
    private static final String PARAMS = "<PARAMS>";

    private static final String POSTARITY = "<POSTARITY>";
    private static final String VALUE_ASSIGNABLES = "<VALUE_ASSIGNABLES>";
    private static final String ACCESSIBLES = "<ACCESSIBLES>";
    private static final String PVS_ANON = "<PVS_ANON>";

    private final InstantiationAspectProverHelper helper;

    private final String keyProveFootprintScaffold;

    public FootprintConditionProver() {
        keyProveFootprintScaffold = KeyBridgeUtils.readResource(FOOTPRINT_PROBLEM_FILE_SCAFFOLD);
        helper = new InstantiationAspectProverHelper();
    }

    public FootprintConditionProver(final Profile profile) {
        keyProveFootprintScaffold = KeyBridgeUtils.readResource(FOOTPRINT_PROBLEM_FILE_SCAFFOLD);
        helper = new InstantiationAspectProverHelper(profile);
    }

    @Override
    public ProofResult prove(AEInstantiationModel model) {
        return model.getApeInstantiations().stream().map(inst -> proveFootprintInst(model, inst))
                .collect(ProofResult.REDUCER);
    }

    @Override
    public String initMessage() {
        return "Proving Footprint Condition(s)...";
    }

    @Override
    public String proofObjective() {
        return "footprint condition(s)";
    }

    /**
     * Attempts to prove that the given instantiation satisfies the frame condition
     * of the APE to instantiate.
     * 
     * @param inst The {@link APEInstantiation}
     * @return A {@link ProofResult} for the frame problem.
     */
    private ProofResult proveFootprintInst(final AEInstantiationModel model,
            APEInstantiation inst) {
        final String keyFileContent = createProveFootprintKeYFile(model, inst);
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

    private String createProveFootprintKeYFile(final AEInstantiationModel model,
            final APEInstantiation inst) {
        final RetrieveProgramResult retrProgRes = helper.retrieveProgram(model,
                inst.getInstantiation());

        final Services services = retrProgRes.getServices();
        final TermBuilder tb = services.getTermBuilder();
        final GoalLocalSpecificationRepository specRepo = retrProgRes.getLocalSpecRepo();

        final String javaDLPreCondRelation = KeyBridgeUtils.createJavaDLPreCondition(
                model.getPreCondition(), model.getProgramVariableDeclarations(),
                model.getAbstractLocationSets(), model.getPredicateDeclarations(),
                model.getFunctionDeclarations(), KeyBridgeUtils.dummyKJT(), services);

        //////////

        final String symInsts = InstantiationAspectProverHelper.createLocSetInstAssumptions(model);

        //////////

        final String assignableValuesTerm;
        final String postarity;

        {
            final List<Term> jmlAssignableTerms = tb
                    .locsetUnionToSet(helper.getJMLAssignableTerm(model, inst, services)).stream()
                    .collect(Collectors.toList());

            // Instantiate abstract location sets
            for (int i = 0; i < jmlAssignableTerms.size(); i++) {
                final List<FunctionInstantiation> functionInstantiations = model
                        .getFunctionInstantiations();
                for (int j = 0; j < functionInstantiations.size(); j++) {

                    final Term assignableTerm;
                    {
                        final Term origTerm = jmlAssignableTerms.get(i);
                        if (origTerm.op() == services.getTypeConverter().getLocSetLDT()
                                .getHasTo()) {
                            assignableTerm = origTerm.sub(0);
                        } else {
                            assignableTerm = origTerm;
                        }
                    }

                    final FunctionInstantiation instantiation = functionInstantiations.get(j);

                    if (assignableTerm.sort() != services.getTypeConverter().getLocSetLDT()
                            .targetSort()
                            || !instantiation.getDeclaration().getResultSortName()
                                    .equals("LocSet")) {
                        continue;
                    }

                    if (assignableTerm.op().name().toString()
                            .equals(functionInstantiations.get(j).getDeclaration().getFuncName())) {
                        final Term instTerm;
                        try {
                            instTerm = KeyBridgeUtils.parseTerm(instantiation.getInstantiation(),
                                    specRepo, services);
                        } catch (RecognitionException e) {
                            throw new InvalidSyntaxException(
                                    "Could not parse instantiation for assignable clause", e);
                        }

                        jmlAssignableTerms.set(i, instTerm);
                    }
                }
            }

            final List<Term> instJmlAssignableTerms = jmlAssignableTerms.stream()
                    .flatMap(assgn -> tb.locsetUnionToSet(assgn).stream())
                    .collect(Collectors.toList());

            postarity = instJmlAssignableTerms.stream().map(str -> "any")
                    .collect(Collectors.joining(", "));

            assignableValuesTerm = instJmlAssignableTerms.stream()
                    .map(assgn -> KeyBridgeUtils.termToString(assgn, services).replaceAll("\n", ""))
                    .map(assgn -> String.format("value(%s)", assgn))
                    .collect(Collectors.joining(", "));
        }

        //////////

        final String accessibles = helper.getJavaDLAccessibleTermString(model, inst, services);

        //////////

        final String pvsAnon;
        final String anonPVDecls;
        final LinkedHashSet<LocationVariable> instProgVars;

        {
            final ProgramVariableCollector progVarCol = new ProgramVariableCollector(
                    retrProgRes.getProgram(), retrProgRes.getLocalSpecRepo(),
                    retrProgRes.getServices());
            progVarCol.start();

            final List<String> ignPVs = Arrays.asList(
                    new String[] { "_result", "_exc", "_objUnderTest", "heap", "savedHeap" });

            instProgVars = progVarCol.result().stream()
                    .filter(lv -> !ignPVs.contains(lv.name().toString()))
                    .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));

            final Map<LocationVariable, String> renameMap = instProgVars.stream()
                    .collect(Collectors.toMap(var -> var,
                            var -> services.getTermBuilder().newName(var.name().toString())));

            final String pvsAnonTmp = instProgVars.stream().map(var -> String.format(
                    "%2$s:=(%1$s) value(singletonPV(anonPV(PV(%2$s),setMinus(allLocs,pvLocs(%3$s)),PV(%4$s))))",
                    var.sort().name().toString(), var.name().toString(), accessibles,
                    renameMap.get(var))).collect(Collectors.joining("||"));

            pvsAnon = pvsAnonTmp.trim().isEmpty() ? "" : "||" + pvsAnonTmp;

            anonPVDecls = renameMap.entrySet().stream().map(
                    p -> String.format("%s %s;", p.getKey().sort().name().toString(), p.getValue()))
                    .collect(Collectors.joining("\n")).trim();

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

            newVars = "\n  " + newInstVars + "\n  " + anonPVDecls;
        }

        return keyProveFootprintScaffold
                .replaceAll(FUNCTIONS,
                        mquote(InstantiationAspectProverHelper.createFuncDecls(model)))
                .replaceAll(PREDICATES,
                        mquote(InstantiationAspectProverHelper.createPredDecls(model)))
                .replaceAll(PROGRAMVARIABLES,
                        mquote(InstantiationAspectProverHelper.createProgvarDecls(model) + newVars))
                .replaceAll(PARAMS, mquote(InstantiationAspectProverHelper.createParams(model)))
                .replaceAll(SYMINSTS, mquote(symInsts))
                .replaceAll(pquote(PRECONDITION), mquote(javaDLPreCondRelation))
                .replaceAll(ADDITIONAL_PREMISES,
                        mquote(KeyBridgeUtils
                                .createAdditionalPremises(model.getAbstractLocationSets())))
                //
                .replaceAll(POSTARITY, mquote(postarity)) //
                .replaceAll(VALUE_ASSIGNABLES, mquote(assignableValuesTerm)) //
                .replaceAll(ACCESSIBLES, mquote(accessibles)) //
                .replaceAll(PVS_ANON, mquote(pvsAnon));
    }

    private static String pquote(final String str) {
        return Pattern.quote(str);
    }

    private static String mquote(final String str) {
        return Matcher.quoteReplacement(str);
    }

}
