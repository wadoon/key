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

import static org.key_project.util.java.FunctionWithException.catchExc;

import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.antlr.runtime.RecognitionException;

import de.uka.ilkd.key.abstractexecution.refinity.keybridge.InvalidSyntaxException;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.ProofResult;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.InstantiationAspectProverHelper.APERetrievalResult;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.APEInstantiation;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.FunctionInstantiation;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.PredicateInstantiation;
import de.uka.ilkd.key.abstractexecution.refinity.util.KeyBridgeUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.GenericTermReplacer;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;

/**
 * Mutual exclusion checking of abrupt completion preconditions.
 * 
 * @author Dominic Steinhoefel
 */
public class PrecMutualExclusionProver implements InstantiationAspectProver {
    private final InstantiationAspectProverHelper helper;

    public PrecMutualExclusionProver() {
        helper = new InstantiationAspectProverHelper();
    }

    public PrecMutualExclusionProver(final Profile profile) {
        helper = new InstantiationAspectProverHelper(profile);
    }

    @Override
    public ProofResult prove(final AEInstantiationModel model) {
        return model.getApeInstantiations().stream().map(inst -> proveHasToInst(model, inst))
                .collect(ProofResult.REDUCER);
    }

    @Override
    public String initMessage() {
        return "Proving " + proofObjective() + "...";
    }

    @Override
    public String proofObjective() {
        return "mutual exclusion of preconditions";
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
        final APERetrievalResult apeRetr = helper.getAPEForInst(model, inst);

        final Services services = apeRetr.getServices();
        final TermBuilder tb = services.getTermBuilder();
        final GoalLocalSpecificationRepository localSpecRepo = apeRetr.getLocalSpecRepo();

        final List<Behavior> behaviors = Arrays
                .asList(new Behavior[] { Behavior.EXCEPTIONAL_BEHAVIOR, Behavior.RETURN_BEHAVIOR,
                        Behavior.BREAK_BEHAVIOR, Behavior.CONTINUE_BEHAVIOR });

        final Map<String, String> funcInstsStr = model.getFunctionInstantiations().stream()
                .collect(Collectors.toMap(finst -> finst.getDeclaration().getName(),
                        FunctionInstantiation::getInstantiation));

        final Map<String, String> predInstsStr = model.getPredicateInstantiations().stream()
                .collect(Collectors.toMap(finst -> finst.getDeclaration().getName(),
                        PredicateInstantiation::getInstantiation));

        final Map<Function, Term> funcPredInsts = Stream
                .concat(funcInstsStr.entrySet().stream(), predInstsStr.entrySet().stream())
                .collect(Collectors.toMap(
                        fpinst -> services.getNamespaces().functions().lookup(fpinst.getKey()),
                        catchExc(
                                fpinst -> (Term) KeyBridgeUtils.parseTerm(fpinst.getValue(),
                                        localSpecRepo, services),
                                "Could not parse function or predicate instantiation")));

        final List<Term> preconditions = helper.getCompletionConditions(model, inst).stream()
                .filter(cond -> behaviors.contains(cond.getBehavior()))
                .map(cond -> cond.getJavaDLPrecondition().orElse("true"))
                .map(catchExc(str -> (Term) KeyBridgeUtils.parseTerm(str, localSpecRepo, services),
                        "Could not parse precondition instantiation"))
                .map(pre -> GenericTermReplacer.replace(pre, t -> funcPredInsts.get(t.op()) != null,
                        t -> funcPredInsts.get(t.op()), services))
                .collect(Collectors.toList());

        Term toProve = tb.tt();

        for (int i = 0; i < preconditions.size(); i++) {
            for (int j = i + 1; j < preconditions.size(); j++) {
                final Term prec1 = preconditions.get(i);
                final Term prec2 = preconditions.get(j);

                toProve = tb.and(toProve, tb.or(tb.not(prec1), tb.not(prec2)));
            }
        }

        if (!model.getPreCondition().trim().isEmpty()) {
            final Term javaDLPreCond;
            try {
                javaDLPreCond = KeyBridgeUtils.parseTerm(KeyBridgeUtils.createJavaDLPreCondition(
                        model.getPreCondition(), model.getProgramVariableDeclarations(),
                        model.getAbstractLocationSets(), model.getPredicateDeclarations(),
                        model.getFunctionDeclarations(), KeyBridgeUtils.dummyKJT(), services),
                        localSpecRepo, services);
            } catch (RecognitionException re) {
                throw new InvalidSyntaxException(
                        "Could not parse specified relational precondition", re);
            }

            toProve = tb.imp(javaDLPreCond, toProve);
        }
        
        // Frequently, the proof is trivial, since many preconditions are false
        if (toProve.op() == Junctor.TRUE) {
            return ProofResult.EMPTY;
        }

        final Proof proof;

        try {
            proof = KeyBridgeUtils.prove(toProve, helper.keyFileHeader(model, inst), 10000,
                    services);
        } catch (ProofInputException e) {
            throw new InvalidSyntaxException(
                    "Problems while proving mutual exclusion of preconditions", e);
        }

        try {
            final File file = KeyBridgeUtils.createTmpDir().resolve("precsMutualExclusion.proof")
                    .toFile();
            proof.setProofFile(null);
            proof.saveToFile(file);
            proof.setProofFile(file);
        } catch (IOException e) {
            throw new RuntimeException("Could not save KeY proof", e);
        }

        return new ProofResult(proof.closed(), proof,
                KeyBridgeUtils.getFilenameForAPEProof(proofObjective(), proof.closed(), inst));
    }

}
