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
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import org.antlr.runtime.RecognitionException;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.HasToLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.SkolemLoc;
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
import de.uka.ilkd.key.logic.OpCollector;
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
        return "footprint condition for abstract symbol instantiations";
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

        final Map<Function, Term> funcPredInsts = funcPredInsts(model, services);

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
                final Term wellformedPrecondition;
                {
                    final Pair<Term, Term> updAndPrec = //
                            anonymizeHeapAndRegister(footprint, newFuncs, services);
                    heapAnonUpd = updAndPrec.first;
                    wellformedPrecondition = updAndPrec.second;
                }

                final Term abstractUpdate = tb.abstractUpdate("anon",
                        footprint.stream().filter(SkolemLoc.class::isInstance)
                                .map(SkolemLoc.class::cast).map(loc -> new HasToLoc<SkolemLoc>(loc))
                                .map(loc -> loc.toTerm(services)).collect(Collectors.toList()),
                        Collections.emptyList());

                final Term funcPredInst = funcPredInsts.get(occ.op());

                final Term pvAnonUpd = //
                        anonPVUpdate(footprint, funcPredInst, behavior, newPVs, services);

                proofObligations.add(tb.imp(wellformedPrecondition,
                        tb.equals(funcPredInst,
                                tb.apply(tb.parallel(abstractUpdate, heapAnonUpd, pvAnonUpd),
                                        funcPredInst))));
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

    /**
     * Anonymizes the heap locations in the footprint and registers the new heap
     * symbol.
     * 
     * @param footprint The footprint locs to anonymize.
     * @param newFuncs The list of functions for registering the new one.
     * @param services The {@link Services} object (for namespaces,
     * {@link TermBuilder})
     * @return A pair of the anonymizing elementary heap update and the
     * wellformedness precondition.
     */
    private Pair<Term, Term> anonymizeHeapAndRegister(final List<AbstractUpdateLoc> footprint,
            final List<Function> newFuncs, final Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final Term heapAnonUpd;
        final Term wellformedPrecondition;
        {
            final LocationVariable heap = (LocationVariable) tb.getBaseHeap().op();
            final Name anonHeapName = new Name(tb.newName("anon_" + heap));
            final Function anonHeapFunc = new Function(anonHeapName, heap.sort());
            services.getNamespaces().functions().addSafely(anonHeapFunc);
            newFuncs.add(anonHeapFunc);

            wellformedPrecondition = tb.and(tb.wellFormed(heap),
                    tb.wellFormed(tb.func(anonHeapFunc)));

            heapAnonUpd = tb.anonUpd(heap,
                    tb.setMinus(tb.allLocs(),
                            tb.union(tb.freshLocs(tb.getBaseHeap()),
                                    tb.union(footprint.stream().filter(HeapLoc.class::isInstance)
                                            .map(HeapLoc.class::cast).map(h -> h.toTerm(services))
                                            .collect(Collectors.toList())))),
                    tb.func(anonHeapFunc));
        }

        return new Pair<>(heapAnonUpd, wellformedPrecondition);
    }

    /**
     * Creates a fresh location variable for the given one and registers it in the
     * services namespaces and the given list of program variables.
     * 
     * @param lv The {@link LocationVariable} to anonymize.
     * @param newPVs The list of new {@link LocationVariable}s.
     * @param services The {@link Services} object (namespaces,
     * {@link TermBuilder}).
     * @return The fresh variale.
     */
    protected LocationVariable anonymizePVAndRegister(LocationVariable lv,
            final List<LocationVariable> newPVs, final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final String anonVarName = new Name(tb.newName("anon_" + lv)).toString();
        final LocationVariable anonLV = new LocationVariable(new ProgramElementName(anonVarName),
                lv.getKeYJavaType());
        services.getNamespaces().programVariables().add(anonLV);
        newPVs.add(anonLV);
        return anonLV;
    }

    /**
     * Creates the anonymizing update of program variables.
     * 
     * @param footprint The footprint locs to anonymize.
     * @param behavior The behavior case, for adding special variables (result,
     * exc).
     * @param services The {@link Services} object.
     * @param pvsInInst The program variables in the instantiation.
     * @return The anonymizing update.
     */
    protected Term anonPVUpdate(final List<AbstractUpdateLoc> footprint, final Term funcPredInst,
            final Behavior behavior, final List<LocationVariable> newPVs, final Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final List<LocationVariable> pvsInInst;
        {
            final OpCollector opColl = new OpCollector();
            funcPredInst.execPostOrder(opColl);
            pvsInInst = opColl.ops().stream().filter(LocationVariable.class::isInstance)
                    .map(LocationVariable.class::cast).collect(Collectors.toList());
        }

        final List<PVLoc> enrichedFootprint = new ArrayList<>();
        {
            footprint.stream().filter(PVLoc.class::isInstance).map(PVLoc.class::cast)
                    .forEach(enrichedFootprint::add);

            switch (behavior) {
            case RETURN_BEHAVIOR:
                enrichedFootprint.add(new PVLoc((LocationVariable) services.getNamespaces()
                        .programVariables().lookup("result")));
                break;
            case EXCEPTIONAL_BEHAVIOR:
                enrichedFootprint.add(new PVLoc((LocationVariable) services.getNamespaces()
                        .programVariables().lookup("exc")));
            default:
                break;
            }
        }

        final Term anonLocs = tb.setMinus(tb.allLocs(), tb.union(enrichedFootprint.stream()
                .map(loc -> loc.toTerm(services)).collect(Collectors.toList())));

        return tb.parallel( //
                pvsInInst.stream()
                        .map(lv -> tb.elementary(tb.var(lv),
                                tb.cast(lv.sort(),
                                        tb.value(tb.singletonPV(tb.anonPV(lv, anonLocs,
                                                anonymizePVAndRegister(lv, newPVs, services)))))))
                        .collect(ImmutableSLList.toImmutableList()));
    }

    /**
     * Computes a map from the symbols instantiated by a function and predicate
     * instantiation to the term to which it is instantiated.
     * 
     * @param model The {@link AEInstantiationModel} for function and predicate
     * instantiations.
     * @param services The {@link Services} object.
     * @return A map from instantiated (non-nullary) function and predicate symbols
     * to their instantiations.
     */
    protected Map<Function, Term> funcPredInsts(final AEInstantiationModel model,
            final Services services) {
        final GoalLocalSpecificationRepository localSpecRepo = new GoalLocalSpecificationRepository();

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

        final Map<Function, Term> funcPredInsts = new LinkedHashMap<>();
        funcPredInsts.putAll(funcInsts);
        funcPredInsts.putAll(predInsts);

        return funcPredInsts;
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
