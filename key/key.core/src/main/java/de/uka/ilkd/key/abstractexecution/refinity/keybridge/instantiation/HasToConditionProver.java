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

import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.stream.Collector;
import java.util.stream.Collectors;

import org.antlr.runtime.RecognitionException;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.HasToLoc;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.InvalidSyntaxException;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.ProofResult;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.RetrieveProgramResult;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.APEInstantiation;
import de.uka.ilkd.key.abstractexecution.refinity.util.KeyBridgeUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;
import de.uka.ilkd.key.util.MiscTools;

/**
 * Checks the Has-To condition of an instantiation..
 * 
 * @author Dominic Steinhoefel
 */
public class HasToConditionProver implements InstantiationAspectProver {
    private static final String KEY_HEADER_SCAFFOLD = "/de/uka/ilkd/key/refinity/instantiation/header.key";

    private static final String PROGRAMVARIABLES = "<PROGRAMVARIABLES>";
    private static final String PREDICATES = "<PREDICATES>";
    private static final String FUNCTIONS = "<FUNCTIONS>";

    private final String keyHeaderScaffold;

    private final InstantiationAspectProverHelper helper;

    public HasToConditionProver() {
        keyHeaderScaffold = KeyBridgeUtils.readResource(KEY_HEADER_SCAFFOLD);
        helper = new InstantiationAspectProverHelper();
    }

    public HasToConditionProver(final Profile profile) {
        keyHeaderScaffold = KeyBridgeUtils.readResource(KEY_HEADER_SCAFFOLD);
        helper = new InstantiationAspectProverHelper(profile);
    }

    @Override
    public ProofResult prove(final AEInstantiationModel model) {
        return model.getApeInstantiations().stream().map(inst -> proveHasToInst(model, inst))
                .collect(ProofResult.REDUCER);
    }

    @Override
    public String initMessage() {
        return "Proving HasTo Condition(s)...";
    }

    @Override
    public String proofObjective() {
        return "HasTo condition(s)";
    }

    /**
     * Attempts to prove that the given instantiation satisfies the hasTo condition
     * of the APE to instantiate.
     * 
     * @param inst The {@link APEInstantiation}
     * @return A {@link ProofResult} for the frame problem.
     */
    private ProofResult proveHasToInst(final AEInstantiationModel model,
            final APEInstantiation inst) {
        final RetrieveProgramResult retrProgRes = //
                helper.retrieveProgram(model, inst.getInstantiation());

        final Services services = retrProgRes.getServices();

        final TermBuilder tb = services.getTermBuilder();

        final Collector<Term, ?, Term> unionReducer = Collectors.reducing(tb.empty(),
                (ls1, ls2) -> tb.union(ls1, ls2));

        final GoalLocalSpecificationRepository localSpecRepo = retrProgRes.getLocalSpecRepo();

        final ImmutableSet<ProgramVariable> outVars = MiscTools
                .getLocalOuts(retrProgRes.getProgram(), localSpecRepo, services);

        if (outVars.isEmpty()) {
            return ProofResult.EMPTY;
        }

        final Term writtenVarsTerm = outVars.stream().map(LocationVariable.class::cast)
                .map(tb::singletonPV).collect(unionReducer);

        final Set<AbstractUpdateLoc> hasToLocs = AbstractUpdateFactory
                .abstrUpdateLocsFromUnionTerm(helper.getJMLAssignableTerm(model, inst, services),
                        Optional.empty(), services)
                .stream().filter(HasToLoc.class::isInstance).map(HasToLoc.class::cast)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));

        if (hasToLocs.isEmpty()) {
            return ProofResult.EMPTY;
        }

        final Term hasToLocsTerm = hasToLocs.stream().map(loc -> loc.toTerm(services))
                .collect(unionReducer);

        final Term assumptionTerm;
        {
            try {
                assumptionTerm = KeyBridgeUtils.parseTerm(//
                        InstantiationAspectProverHelper.createLocSetInstAssumptions(model), localSpecRepo,
                        services);
            } catch (RecognitionException re) {
                throw new InvalidSyntaxException(re.getMessage(), re.getCause());
            }
        }

        final Term proofTerm = tb.imp(assumptionTerm, tb.subset(hasToLocsTerm, writtenVarsTerm));

        Proof proof;
        try {
            proof = KeyBridgeUtils.prove(proofTerm, keyFileHeader(model, inst), 10000, services);
        } catch (ProofInputException e) {
            throw new InvalidSyntaxException("Problems while proving hasTo condition", e);
        }

        try {
            final File file = KeyBridgeUtils.createTmpDir().resolve("hasToProof.proof").toFile();
            proof.setProofFile(null);
            proof.saveToFile(file);
            proof.setProofFile(file);
        } catch (IOException e) {
            throw new RuntimeException("Could not save KeY proof", e);
        }

        if (!proof.closed()) {
            System.err.println("[INFO] Possible incompleteness issue with HasTo prover:\n"
                    + "The HasTo prover is sound, but incomplete, since it only extracts\n"
                    + "assigned program variables, and not heap locations, from instantiations.");
        }

        return new ProofResult(proof.closed(), proof,
                KeyBridgeUtils.getFilenameForAPEProof(proofObjective(), proof.closed(), inst));
    }

    /**
     * Returns a header for a KeY proof, including declarations of variables in the
     * instantiation.
     * 
     * @param inst The instantiation (for declaring free variables).
     * @return The header.
     */
    private String keyFileHeader(final AEInstantiationModel model, final APEInstantiation inst) {
        final LinkedHashSet<LocationVariable> instProgVars;

        {
            final RetrieveProgramResult retrProgRes = helper.retrieveProgram(model,
                    inst.getInstantiation());
            final ProgramVariableCollector progVarCol = new ProgramVariableCollector(
                    retrProgRes.getProgram(), retrProgRes.getLocalSpecRepo(),
                    retrProgRes.getServices());
            progVarCol.start();

            final List<String> ignPVs = Arrays
                    .asList(new String[] { "_result", "_exc", "_objUnderTest" });

            instProgVars = progVarCol.result().stream()
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

        return keyHeaderScaffold
                .replaceAll(FUNCTIONS,
                        Matcher.quoteReplacement(
                                InstantiationAspectProverHelper.createFuncDecls(model)))
                .replaceAll(PREDICATES,
                        Matcher.quoteReplacement(
                                InstantiationAspectProverHelper.createPredDecls(model)))
                .replaceAll(PROGRAMVARIABLES, Matcher.quoteReplacement(
                        InstantiationAspectProverHelper.createProgvarDecls(model) + newVars));
    }

}
