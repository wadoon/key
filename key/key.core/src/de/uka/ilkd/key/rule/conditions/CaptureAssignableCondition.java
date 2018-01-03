// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.AssignableScopeBlock;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.ContextInstantiationEntry;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * This variable condition ensures that no other label of the
 * same name exists in the context program or one of the schemavariable
 * instantiations.
 */
public final class CaptureAssignableCondition implements VariableCondition {

    private final TermSV assignableSV;
    private final ProgramSV programElement;

    public CaptureAssignableCondition(ProgramSV programElement, TermSV sv) {
        this.programElement = programElement;
        this.assignableSV = sv;
    }

    @Override
    public MatchConditions check(SchemaVariable var,
            SVSubstitute instCandidate, MatchConditions matchCond,
            Services services) {

        System.out.println(var + "->" + instCandidate);

        Object instantiation = matchCond.getInstantiations().getInstantiation(assignableSV);
        if(instantiation != null)
            return matchCond;

        ContextInstantiationEntry contextInst = matchCond.getInstantiations().getContextInstantiation();
        ProgramElement program = contextInst.contextProgram();
        PosInProgram pos = contextInst.prefix();

        while(pos.depth() > 0) {
            ProgramElement current = pos.getProgram(program);
            if(current instanceof AssignableScopeBlock) {
                AssignableScopeBlock ass = (AssignableScopeBlock) current;
                Term t = services.getTermFactory().createTerm(ass.getAssignablePV());
                return updateInst(matchCond, t, services);
            }
            pos = pos.up();
        }

        Term t = services.getTermBuilder().allLocs();
        return updateInst(matchCond, t, services);
    }

    private MatchConditions updateInst(MatchConditions matchCond, Term t,
            Services services) {
        SVInstantiations inst = matchCond.getInstantiations();
        inst = inst.add(assignableSV, t, services);
        return matchCond.setInstantiations(inst);
    }

    @Override
    public String toString() {
        return "\\captureAssignableScope(" + programElement + ", " + assignableSV + ")";
    }
}