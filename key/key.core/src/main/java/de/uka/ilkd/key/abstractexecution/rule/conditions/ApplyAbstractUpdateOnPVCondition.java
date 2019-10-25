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

import java.util.List;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateAssgnLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.HasToLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Variable condition for an abstract update on a program variable in certain
 * situations. Schematically:
 * <code>{U_P(empty, y!:=x, w)}y --> f_P_2(x, w)</code>, where f_P_2 is a fresh
 * symbol generated for the 2nd position in update U_P.
 *
 * @author Dominic Steinhoefel
 */
public final class ApplyAbstractUpdateOnPVCondition implements VariableCondition {
    private final UpdateSV updateSV;
    private final ProgramSV pvSV;
    private final SchemaVariable resultSV;

    public ApplyAbstractUpdateOnPVCondition(UpdateSV updateSV, ProgramSV pvSV,
            SchemaVariable resultSV) {
        this.updateSV = updateSV;
        this.pvSV = pvSV;
        this.resultSV = resultSV;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate, MatchConditions mc,
            Services services) {
        final SVInstantiations svInst = mc.getInstantiations();

        final Term updateTerm = (Term) svInst.getInstantiation(updateSV);
        final Term pvTerm = (Term) svInst.getInstantiation(pvSV);
        final Term origResult = (Term) svInst.getInstantiation(resultSV);

        if (updateTerm == null || pvTerm == null || !(updateTerm.op() instanceof AbstractUpdate)
                || !(pvTerm.op() instanceof LocationVariable)) {
            return null;
        }

        if (origResult != null) {
            return mc;
        }

        final AbstractUpdateFactory abstractUpdateFactory = services.abstractUpdateFactory();
        final TermBuilder tb = services.getTermBuilder();

        final AbstractUpdate abstrUpd = (AbstractUpdate) updateTerm.op();
        final List<AbstractUpdateAssgnLoc> allAssignables = abstrUpd.getAllAssignables();
        final LocationVariable locVar = (LocationVariable) pvTerm.op();

        for (int i = 0; i < allAssignables.size(); i++) {
            final AbstractUpdateAssgnLoc assignable = allAssignables.get(i);
            if (assignable instanceof HasToLoc
                    && assignable.mayAssign(new PVLoc(locVar), services)) {
                final Term replacement = tb.func(
                        abstractUpdateFactory.getCharacteristicFunctionForPosition(abstrUpd, i),
                        updateTerm.subs().toArray(new Term[0]));

                return mc.setInstantiations(svInst.add(resultSV, replacement, services));
            }
        }

        return null;
    }

    @Override
    public String toString() {
        return String.format("\\applyAbstractUpdateOnPV(%s, %s, %s)", updateSV, pvSV, resultSV);
    }

}