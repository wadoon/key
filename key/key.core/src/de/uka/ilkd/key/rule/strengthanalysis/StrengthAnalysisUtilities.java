// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.strengthanalysis;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.util.Pair;

/**
 * TODO
 *
 * @author Dominic Steinhöfel
 */
public class StrengthAnalysisUtilities {

    /**
     * TODO
     * 
     * @param services
     * @param pm
     * @param origHeapTerm
     * @return
     */
    public static Pair<Term, List<Term>> extractStoreEqsAndInnerHeapTerm(
            Services services, final IProgramMethod pm,
            final Term origHeapTerm) {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final TermBuilder tb = services.getTermBuilder();

        final List<Term> storeEqualities = new ArrayList<>();
        Term innerHeapTerm = origHeapTerm;
        if (!pm.isStatic()) {
            // TODO Should we also check whether pm is pure? How to do this?

            // TODO: Is it justified to assume that a heap is of the form
            // store(store(...(anon/heap...))), i.e. if there is a store,
            // then we have a store sequence at the beginning?
            Term currHeapTerm = innerHeapTerm;
            while (currHeapTerm.op() == heapLDT.getStore()) {
                final Term targetObj = currHeapTerm.sub(1);
                final Term field = currHeapTerm.sub(2);
                final Term value = currHeapTerm.sub(3);

                // Note: value could contain method-local variables, in which
                // case the fact is likely to be uncovered by the post
                // condition. Still, we don't remove it, since then indeed, this
                // reflects behavior that is not shown to the outside, and thus
                // indicates that we're not using the strongest possible post
                // condition.

                storeEqualities.add(tb.equals(tb.select(value.sort(),
                        tb.getBaseHeap(), targetObj, field), value));

                currHeapTerm = currHeapTerm.sub(0);
            }

            // Here, currHeapTerm should be the "core" without any stores.
            innerHeapTerm = currHeapTerm;
        }
        return new Pair<Term, List<Term>>(innerHeapTerm, storeEqualities);
    }

    /**
     * TODO
     * 
     * @param services
     * @return
     */
    public static FunctionalOperationContract getFOContract(Services services) {
        final ContractPO contractPO = services.getSpecificationRepository()
                .getContractPOForProof(services.getProof());
        assert contractPO != null
                && contractPO instanceof FunctionalOperationContractPO;
        final FunctionalOperationContract fContract = //
                ((FunctionalOperationContractPO) contractPO).getContract();
        return fContract;
    }

    /**
     * TODO
     * 
     * @param pio
     * @param services
     * @return
     */
    public static Optional<LocationVariable> retrieveLoopScopeIndex(
            PosInOccurrence pio, Services services) {
        final Optional<LocationVariable> failedResult = Optional.empty();

        final Term formula;
        if (pio == null //
                || !pio.isTopLevel() //
                || (formula = pio.subTerm()).containsJavaBlockRecursive()
                || !(formula.op() instanceof UpdateApplication)) {
            return failedResult;
        }

        // @formatter:off
        
        // Expected structure:
        // {U}((x<<loopScopeIndex>> = TRUE  -> ...) & 
        //      x<<loopScopeIndex>> = FALSE -> ...)
        
        // @formatter:on

        if (formula.sub(1).op() != Junctor.AND
                || formula.sub(1).sub(0).op() != Junctor.IMP
                || formula.sub(1).sub(1).op() != Junctor.IMP
                || formula.sub(1).sub(0).sub(0).op() != Equality.EQUALS
                || formula.sub(1).sub(1).sub(0).op() != Junctor.NOT || formula
                        .sub(1).sub(1).sub(0).sub(0).op() != Equality.EQUALS) {
            return failedResult;
        }

        final Term loopScopeVar = formula.sub(1).sub(0).sub(0).sub(0);
        final Term negatedLoopScopeVar = formula.sub(1).sub(0).sub(0).sub(0);

        if (!(loopScopeVar.op() instanceof LocationVariable)
                || !loopScopeVar.hasLabels()
                || loopScopeVar.getLabel(
                        ParameterlessTermLabel.LOOP_SCOPE_INDEX_LABEL_NAME) == null
                || loopScopeVar != negatedLoopScopeVar) {
            return failedResult;
        }

        return Optional.of((LocationVariable) loopScopeVar.op());
    }

    /**
     * 
     * TODO
     * 
     * @param pio
     * @param analysisGoal
     * @param fact
     * @param descr
     */
    public static void prepareGoal(final PosInOccurrence pio,
            final Goal analysisGoal, final Term fact, final String descr) {
        final Services services = analysisGoal.proof().getServices();

        analysisGoal.setBranchLabel(String.format("%s \"%s\"", descr,
                LogicPrinter.quickPrintTerm(fact, services)
                        .replaceAll("(\\r|\\n|\\r\\n)+", "").trim()));

        analysisGoal.removeFormula(pio);
        analysisGoal.addFormula(new SequentFormula(fact), false, true);
    }

    /**
     * TODO
     * 
     * @param pio
     * @param analysisGoal
     * @param fact
     */
    public static void prepareGoal(final PosInOccurrence pio,
            final Goal analysisGoal, final Term fact) {
        prepareGoal(pio, analysisGoal, fact, "Covers fact");
    }

}
