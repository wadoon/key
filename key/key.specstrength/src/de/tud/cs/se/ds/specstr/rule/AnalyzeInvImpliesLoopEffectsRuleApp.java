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

package de.tud.cs.se.ds.specstr.rule;

import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import org.key_project.util.collection.ImmutableList;

import de.tud.cs.se.ds.specstr.util.LogicUtilities;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.AbstractLoopInvariantRule;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.LoopScopeInvariantRule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.LoopSpecification;

/**
 * The {@link RuleApp} for the {@link AnalyzeInvImpliesLoopEffectsRule}.
 *
 * @author Dominic Steinhoefel
 */
public class AnalyzeInvImpliesLoopEffectsRuleApp
        extends AbstractBuiltInRuleApp {

    /**
     * The invariant {@link Term} (without updates).
     */
    private final Term invTerm;

    /**
     * The local out {@link LocationVariable}s of the loop, that is those that
     * are accessible from the outside.
     */
    private final List<LocationVariable> localOuts;

    /**
     * The {@link Node} with the {@link LoopScopeInvariantRule} application for
     * the loop the effects of are to be studied here.
     */
    private final Node loopInvNode;

    /**
     * Constructor.
     *
     * @param rule
     *            The {@link BuiltInRule} for this app (an
     *            {@link AnalyzeInvImpliesLoopEffectsRule}).
     * @param pio
     *            The {@link PosInOccurrence} of the rule application.
     * @param invTerm
     *            The invariant {@link Term} (without updates).
     * @param localOuts
     *            The local out {@link LocationVariable}s of the loop, that is
     *            those that are accessible from the outside.
     * @param loopInvNode
     *            The {@link Node} with the {@link LoopScopeInvariantRule}
     *            application for the loop the effects of are to be studied
     *            here.
     */
    protected AnalyzeInvImpliesLoopEffectsRuleApp(BuiltInRule rule,
            PosInOccurrence pio, Term invTerm, List<LocationVariable> localOuts,
            Node loopInvNode) {
        super(rule, pio);
        this.invTerm = invTerm;
        this.localOuts = localOuts;
        this.loopInvNode = loopInvNode;
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
        return super.complete() && invTerm != null && localOuts != null;
    }

    @Override
    public AbstractBuiltInRuleApp tryToInstantiate(Goal goal) {
        final Services services = goal.proof().getServices();

        final LocationVariable loopScopeIdxVar = //
                LogicUtilities.findLoopScopeIndexVar(goal.node());

        if (loopScopeIdxVar == null) {
            return null;
        }

        // Find loop where the loop scope index was introduced
        final Node loopInvNode = LogicUtilities
                .findCorrespondingLoopInvNode(goal.node(), loopScopeIdxVar);

        if (loopInvNode == null) {
            return null;
        }

        final LoopInvariantBuiltInRuleApp loopInvApp = //
                (LoopInvariantBuiltInRuleApp) loopInvNode.getAppliedRuleApp();

        final LoopSpecification loopSpec = loopInvApp
                .retrieveLoopInvariantFromSpecification(services);

        final JavaBlock javaBlock = TermBuilder
                .goBelowUpdates(
                    loopInvApp.posInOccurrence().sequentFormula().formula())
                .javaBlock();
        Term lLoopInvTerm = AbstractLoopInvariantRule.conjunctInv(services,
            loopInvApp.getHeapContext(), loopSpec, javaBlock);

        List<LocationVariable> lLocalOuts = StreamSupport
                .stream(loopSpec.getLocalOuts().spliterator(), true)
                .map(t -> (LocationVariable) t.op())
                .collect(Collectors.toList());

        return new AnalyzeInvImpliesLoopEffectsRuleApp(this.builtInRule,
            this.pio, lLoopInvTerm, lLocalOuts, loopInvNode);
    }

    public Term getInvTerm() {
        return invTerm;
    }

    public List<LocationVariable> getLocalOuts() {
        return localOuts;
    }

    public Node getLoopInvNode() {
        return loopInvNode;
    }

}
