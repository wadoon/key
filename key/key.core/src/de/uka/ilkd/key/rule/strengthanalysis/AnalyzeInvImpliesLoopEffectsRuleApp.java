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

import java.util.List;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;

/**
 * TODO
 *
 * @author Dominic Steinhöfel
 */
public class AnalyzeInvImpliesLoopEffectsRuleApp
        extends AbstractBuiltInRuleApp {

    private final Term invTerm;
    private final List<LocationVariable> localOuts;

    /**
     * @param rule
     * @param pio
     * @param localOuts 
     */
    protected AnalyzeInvImpliesLoopEffectsRuleApp(BuiltInRule rule,
            PosInOccurrence pio, Term invTerm, List<LocationVariable> localOuts) {
        super(rule, pio);
        this.invTerm = invTerm;
        this.localOuts = localOuts;
    }

    @Override
    public AbstractBuiltInRuleApp replacePos(PosInOccurrence newPos) {
        return null;
    }

    @Override
    public IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
    }

    @Override
    public boolean complete() {
        return super.complete() && invTerm != null;
    }

    @Override
    public AbstractBuiltInRuleApp tryToInstantiate(Goal goal) {
        return null;
    }

    public Term getInvTerm() {
        return invTerm;
    }

    public List<LocationVariable> getLocalOuts() {
        return localOuts;
    }

}
