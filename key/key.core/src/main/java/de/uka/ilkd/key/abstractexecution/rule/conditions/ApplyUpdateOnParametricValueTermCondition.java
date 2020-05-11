// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
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

import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.GenericTermReplacer;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * @author Dominic Steinhoefel
 *
 */
public class ApplyUpdateOnParametricValueTermCondition implements VariableCondition {
    private final UpdateSV updSV;
    private final SchemaVariable paramSkLsSV;
    private final SchemaVariable resultSV;

    public ApplyUpdateOnParametricValueTermCondition(UpdateSV updSV, SchemaVariable paramSkLsSV,
            SchemaVariable resultSV) {
        this.updSV = updSV;
        this.paramSkLsSV = paramSkLsSV;
        this.resultSV = resultSV;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Goal goal, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();
        final TermBuilder tb = services.getTermBuilder();

        if (svInst.getInstantiation(resultSV) != null) {
            return matchCond;
        }

        final Term update = (Term) svInst.getInstantiation(updSV);
        final Term paramSkLs = (Term) svInst.getInstantiation(paramSkLsSV);

        if (update == null || paramSkLs == null) {
            return null;
        }

        // Check if update is in PNF
        if (!MergeRuleUtils.isUpdateNormalForm(update, true)) {
            return null;
        }

        // Check if paramSkLs has the form "someFunc(x)", where "x" is a PV of type int
        if (paramSkLs.arity() != 1 || paramSkLs.sub(0).sort() != services.getTypeConverter()
                .getIntegerLDT().targetSort()
                || !(paramSkLs.sub(0).op() instanceof LocationVariable)) {
            return null;
        }

        final LocationVariable argVar = (LocationVariable) paramSkLs.sub(0).op();

        final List<Term> elemUpdates = MergeRuleUtils.getElementaryUpdates(update, false, tb);

        final Deque<Term> newElemUpdates = new LinkedList<>();
        Term newParamSkLsTerm = null;
        for (int i = elemUpdates.size() - 1; i >= 0; i--) {
            final Term elem = elemUpdates.get(i);

            if (newParamSkLsTerm == null && elem.op() instanceof ElementaryUpdate
                    && ((ElementaryUpdate) elem.op()).lhs() == argVar) {
                newParamSkLsTerm = GenericTermReplacer.replace(paramSkLs, t -> t.op() == argVar,
                        t -> elem.sub(0), services);
                continue;
            }

            newElemUpdates.addFirst(elem);
        }

        if (newParamSkLsTerm == null) {
            return null;
        }

        final Term newUpdate = tb
                .parallel(newElemUpdates.stream().collect(ImmutableSLList.toImmutableList()));
        return matchCond.setInstantiations(
                svInst.add(resultSV, tb.apply(newUpdate, tb.value(newParamSkLsTerm)), services));
    }

    @Override
    public String toString() {
        return String.format(//
                "\\applyUpdateOnParametricValueTerm(%s,%s,%s)", updSV, paramSkLsSV, resultSV);
    }

}