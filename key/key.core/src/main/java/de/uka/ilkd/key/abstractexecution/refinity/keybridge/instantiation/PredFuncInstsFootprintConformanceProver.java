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
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import org.antlr.runtime.RecognitionException;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.heap.HeapLoc;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.CompletionCondition;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.InvalidSyntaxException;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.ProofResult;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.InstantiationAspectProverHelper.APERetrievalResult;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.APEInstantiation;
import de.uka.ilkd.key.abstractexecution.refinity.util.KeyBridgeUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.FilterVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.util.LinkedHashMap;
import de.uka.ilkd.key.util.Pair;

/**
 * Proves conformance of predicate and function instantiations with their
 * footprint, e.g., "returnsA(x, y)" may only depend on x and y, plus possible
 * special variables like "result" and "exc". Only checks symbols directly used
 * in APE specs.
 * 
 * @author Dominic Steinhoefel
 */
public class PredFuncInstsFootprintConformanceProver implements InstantiationAspectProver {
    private final InstantiationAspectProverHelper helper;

    public PredFuncInstsFootprintConformanceProver() {
        helper = new InstantiationAspectProverHelper();
    }

    public PredFuncInstsFootprintConformanceProver(final Profile profile) {
        helper = new InstantiationAspectProverHelper(profile);
    }

    @Override
    public String initMessage() {
        return "Proving " + proofObjective() + "...";
    }

    @Override
    public String proofObjective() {
        return "conformance of abstract symbol instantiations footprints";
    }

    @Override
    public ProofResult prove(final AEInstantiationModel model) {
        return model.getApeInstantiations().stream()
                .map(inst -> proveAbstrSymbInstsFootprintConformance(model, inst))
                .collect(ProofResult.REDUCER);
    }

    /**
     * @param inst The {@link APEInstantiation}
     * @return A {@link ProofResult} for the frame problem.
     */
    private ProofResult proveAbstrSymbInstsFootprintConformance(final AEInstantiationModel model,
            final APEInstantiation inst) {
        final APERetrievalResult apeRetr = helper.getAPEForInst(model, inst);

        final Services services = apeRetr.getServices();
        final TermBuilder tb = services.getTermBuilder();
        final GoalLocalSpecificationRepository localSpecRepo = apeRetr.getLocalSpecRepo();

        final Map<Function, Term> funcPredInsts;
        {
            final Map<Function, Term> funcInsts = model.getFunctionInstantiations().stream()
                    .filter(finst -> !finst.getDeclaration().getArgSorts().isEmpty())
                    .collect(Collectors.toMap(
                            finst -> services.getNamespaces().functions()
                                    .lookup(finst.getDeclaration().getName()),
                            catchExc(
                                    finst -> KeyBridgeUtils.parseTerm(finst.getInstantiation(),
                                            localSpecRepo, services),
                                    "Could not parse function or predicate instantiation")));

            final Map<Function, Term> predInsts = model.getPredicateInstantiations().stream()
                    .filter(pinst -> !pinst.getDeclaration().getArgSorts().isEmpty())
                    .collect(Collectors.toMap(
                            pinst -> services.getNamespaces().functions()
                                    .lookup(pinst.getDeclaration().getName()),
                            catchExc(
                                    pinst -> KeyBridgeUtils.parseTerm(pinst.getInstantiation(),
                                            localSpecRepo, services),
                                    "Could not parse function or predicate instantiation")));

            funcPredInsts = new LinkedHashMap<>();
            funcPredInsts.putAll(funcInsts);
            funcPredInsts.putAll(predInsts);
        }

        final java.util.function.Function<String, Term> parse = catchExc(
                str -> KeyBridgeUtils.parseTerm(str, localSpecRepo, services));

        final Map<Behavior, Pair<Term, Term>> specifiedConditions = helper
                .getCompletionConditions(model, inst).stream()
                .collect(Collectors.toMap(CompletionCondition::getBehavior,
                        cond -> new Pair<>(parse.apply(cond.getJavaDLPrecondition().orElse("true")),
                                parse.apply(cond.getJavaDLPostcondition().orElse("true")))));

        final List<Term> proofObligations = new ArrayList<>();

        final List<LocationVariable> newPVs = new ArrayList<>();
        final List<Function> newFuncs = new ArrayList<>();

        for (final Behavior behavior : specifiedConditions.keySet()) {
            final FilterVisitor fv = new FilterVisitor(
                    t -> funcPredInsts.keySet().contains(t.op()));
            specifiedConditions.get(behavior).first.execPostOrder(fv);
            specifiedConditions.get(behavior).second.execPostOrder(fv);

            for (final Term occ : fv.result()) {
                final List<AbstractUpdateLoc> footprint = occ.subs().stream()
                        .map(sub -> extractLoc(sub, services)).collect(Collectors.toList());

                final Term heapAnonUpd;
                final LocationVariable heap;
                final Function anonHeapFunc;
                {
                    heap = (LocationVariable) tb.getBaseHeap().op();
                    final Name anonHeapName = new Name(tb.newName("anon_" + heap));
                    anonHeapFunc = new Function(anonHeapName, heap.sort());
                    services.getNamespaces().functions().addSafely(anonHeapFunc);
                    newFuncs.add(anonHeapFunc);

                    heapAnonUpd = tb.anonUpd(heap,
                            tb.setMinus(tb.allLocs(), tb.union(tb.freshLocs(tb.getBaseHeap()),
                                    tb.union(footprint.stream().filter(HeapLoc.class::isInstance)
                                            .map(HeapLoc.class::cast).map(h -> h.toTerm(services))
                                            .collect(Collectors.toList())))),
                            tb.func(anonHeapFunc));
                }

                final java.util.function.Function<LocationVariable, LocationVariable> anon = lv -> {
                    final String anonVarName = new Name(tb.newName("anon_" + lv)).toString();
                    final LocationVariable anonLV = new LocationVariable(
                            new ProgramElementName(anonVarName), lv.getKeYJavaType());
                    services.getNamespaces().programVariables().add(anonLV);
                    newPVs.add(anonLV);
                    return anonLV;
                };

                final Term pvAnonUpd = tb.parallel(
                        footprint.stream().filter(PVLoc.class::isInstance).map(PVLoc.class::cast)
                                .map(pvLoc -> pvLoc.getVar()).map(lv -> tb.elementary(tb.var(lv), //
                                        tb.cast(lv.sort(), tb.value(tb.singletonPV(tb.anonPV(lv, //
                                                tb.setMinus(tb.allLocs(),
                                                        tb.union(footprint.stream()
                                                                .filter(PVLoc.class::isInstance)
                                                                .map(PVLoc.class::cast)
                                                                .map(loc -> loc.toTerm(services))
                                                                .collect(Collectors.toList()))),
                                                anon.apply(lv)))))))
                                .collect(ImmutableSLList.toImmutableList()));

                final Term predInst = funcPredInsts.get(occ.op());

                proofObligations.add(
                        tb.imp(tb.and(tb.wellFormed(heap), tb.wellFormed(tb.func(anonHeapFunc))),
                                tb.equals(predInst,
                                        tb.apply(tb.parallel(heapAnonUpd, pvAnonUpd), predInst))));
            }
        }

        Term precondition = tb.tt();
        if (!model.getPreCondition().trim().isEmpty()) {
            try {
                precondition = KeyBridgeUtils.parseTerm(KeyBridgeUtils.createJavaDLPreCondition(
                        model.getPreCondition(), model.getProgramVariableDeclarations(),
                        model.getAbstractLocationSets(), model.getPredicateDeclarations(),
                        model.getFunctionDeclarations(), KeyBridgeUtils.dummyKJT(), services),
                        localSpecRepo, services);
            } catch (RecognitionException re) {
                throw new InvalidSyntaxException(
                        "Could not parse specified relational precondition", re);
            }
        }

        final Term toProve = tb.imp(precondition, tb.and(proofObligations));

        /////////////////// PROOF ///////////////////

        final Proof proof;
        try {
            proof = KeyBridgeUtils.prove(toProve,
                    helper.keyFileHeader(model, inst, newPVs, newFuncs), 10000, services);
        } catch (ProofInputException e) {
            throw new InvalidSyntaxException(
                    "Problems while proving mutual exclusion of preconditions", e);
        }

        try {
            final File file = KeyBridgeUtils.createTmpDir()
                    .resolve("abstrSymbInstsFootprintConformance.proof").toFile();
            proof.setProofFile(null);
            proof.saveToFile(file);
            proof.setProofFile(file);
        } catch (IOException e) {
            throw new RuntimeException("Could not save KeY proof", e);
        }

        return new ProofResult(proof.closed(), proof,
                KeyBridgeUtils.getFilenameForAPEProof(proofObjective(), proof.closed(), inst));
    }

    private static AbstractUpdateLoc extractLoc(final Term t, final Services services) {
        if (t.op() instanceof SortDependingFunction
                && SortDependingFunction.getFirstInstance(AbstractSort.CAST_NAME, services)
                        .isSimilar((SortDependingFunction) t.op())) {
            return extractLoc(t.sub(0), services);
        }

        if (t.op() == services.getTypeConverter().getLocSetLDT().getValue()) {
            return extractLoc(t.sub(0), services);
        }

        return AbstractUpdateFactory.abstrUpdateLocFromTerm(t, Optional.empty(), services);
    }

}
