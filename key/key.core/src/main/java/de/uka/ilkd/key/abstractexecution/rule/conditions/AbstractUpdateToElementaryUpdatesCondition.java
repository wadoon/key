// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.abstractexecution.rule.conditions;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.HasToLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.IrrelevantAssignable;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.heap.FieldLoc;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Transforms an {@link AbstractUpdate} like
 * <code>U_P(x!,y!,someloc:=accessibles)</code> to a parallel update
 * <code>U_P(x,y,someloc:=accessibles)||x:=f_P_1(accessibles)||y:=f_P_2(accessibles)</code>.
 * Since the update it parallel, it doesn't matter whether x, someloc are in
 * accessibles or not. Note that the {@link HasToLoc}s are converted to normal
 * locations. This is necessary to prevent endless loops of extracting
 * elementary updates and simplifying them away again.
 * 
 * <p>
 * Only works for {@link PVLoc}s, i.e., x and y above really has to be a
 * location variable and may not, e.g., be an abstract Skolem location term.
 * Extracted are only {@link HasToLoc}s, because others don't have to be
 * written.
 *
 * @author Dominic Steinhoefel
 */
public final class AbstractUpdateToElementaryUpdatesCondition implements VariableCondition {
    private final UpdateSV updateSV;
    private final UpdateSV resultSV;

    public AbstractUpdateToElementaryUpdatesCondition(UpdateSV updateSV, UpdateSV resultSV) {
        this.updateSV = updateSV;
        this.resultSV = resultSV;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate, MatchConditions mc,
            Services services) {
        final SVInstantiations svInst = mc.getInstantiations();

        final Term updateTerm = (Term) svInst.getInstantiation(updateSV);
        final Term origResult = (Term) svInst.getInstantiation(resultSV);

        if (updateTerm == null || !(updateTerm.op() instanceof AbstractUpdate)) {
            return null;
        }

        if (origResult != null) {
            return mc;
        }

        final AbstractUpdateFactory abstractUpdateFactory = services.abstractUpdateFactory();
        final TermBuilder tb = services.getTermBuilder();

        final AbstractUpdate abstrUpd = (AbstractUpdate) updateTerm.op();
        final List<AbstractUpdateLoc> allAssignables = abstrUpd.getAllAssignables();

        ImmutableList<Term> extractedElementaries = ImmutableSLList.<Term>nil();
        final Map<HasToLoc<?>, AbstractUpdateLoc> extractedHasTosMap = new LinkedHashMap<>();

        for (int i = 0; i < allAssignables.size(); i++) {
            final AbstractUpdateLoc assignable = allAssignables.get(i);
            if (assignable instanceof HasToLoc) {
                final AbstractUpdateLoc unwrappedLoc = //
                        AbstractExecutionUtils.unwrapHasTo(assignable);

                if (unwrappedLoc instanceof PVLoc) {
                    @SuppressWarnings("unchecked")
                    final HasToLoc<PVLoc> castAssignable = (HasToLoc<PVLoc>) assignable;
                    final PVLoc pvLoc = castAssignable.child();
                    extractedHasTosMap.put(castAssignable,
                            new IrrelevantAssignable(i, pvLoc.sort()));

                    final Term updateLHS = tb.var(pvLoc.getVar());
                    final Term updateRHS = tb.func(
                            abstractUpdateFactory.getCharacteristicFunctionForPosition(abstrUpd, i),
                            updateTerm.subs().toArray(new Term[0]));
                    extractedElementaries = extractedElementaries
                            .append(tb.elementary(updateLHS, updateRHS));
                } else if (unwrappedLoc instanceof FieldLoc) {
                    @SuppressWarnings("unchecked")
                    final HasToLoc<FieldLoc> castAssignable = (HasToLoc<FieldLoc>) assignable;
                    final FieldLoc fieldLoc = castAssignable.child();
                    extractedHasTosMap.put(castAssignable,
                            new IrrelevantAssignable(i, fieldLoc.sort()));

                    final Term updateLHS = tb.getBaseHeap();
                    final Term characteristicFunctionTerm = tb.func(
                            abstractUpdateFactory.getCharacteristicFunctionForPosition(abstrUpd, i),
                            updateTerm.subs().toArray(new Term[0]));
                    final Term updateRHS = tb.store(tb.getBaseHeap(), fieldLoc.getObjTerm(),
                            fieldLoc.getFieldTerm(), characteristicFunctionTerm);
                    extractedElementaries = extractedElementaries
                            .append(tb.elementary(updateLHS, updateRHS));
                }
            }
        }

        if (extractedElementaries.isEmpty()) {
            return null;
        }

        if (extractedElementaries.size() < allAssignables.size()) {
            extractedElementaries = extractedElementaries
                    .prepend(tb.changeAbstractUpdateAssignables(updateTerm, extractedHasTosMap));
        }

        return mc.setInstantiations(
                svInst.add(resultSV, tb.parallel(extractedElementaries), services));
    }

    @Override
    public String toString() {
        return String.format("\\abstractUpdateToElementaryUpdates(%s, %s)", updateSV, resultSV);
    }

}