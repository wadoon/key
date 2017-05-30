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
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.AbstractLoopInvariantRule.LoopInvariantInformation;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.LoopScopeInvariantRule;
import de.uka.ilkd.key.rule.RuleAbortException;

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
            PosInOccurrence pio, Term invTerm,
            List<LocationVariable> localOuts) {
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
        return super.complete() && invTerm != null && localOuts != null;
    }

    @Override
    public AbstractBuiltInRuleApp tryToInstantiate(Goal goal) {
        final Services services = goal.proof().getServices();
        LocationVariable loopScopeIdxVar = null;

        for (SequentFormula sf : goal.node().sequent().succedent()) {
            Optional<LocationVariable> maybeIdxVar = AnalyzeInvImpliesLoopEffectsRule
                    .retrieveLoopScopeIndex(new PosInOccurrence(sf,
                            PosInTerm.getTopLevel(), false), services);

            if (maybeIdxVar.isPresent()) {
                loopScopeIdxVar = maybeIdxVar.get();
                break;
            }
        }

        if (loopScopeIdxVar == null) {
            return null;
        }

        // Find loop where the loop scope index was introduced
        Node currNode = goal.node().parent();
        while (!currNode.root()) {
            if (currNode.getAppliedRuleApp()
                    .rule() == LoopScopeInvariantRule.INSTANCE
                    && !currNode.getLocalProgVars().contains(loopScopeIdxVar)) {

                Optional<While> maybeWhile = StreamSupport
                        .stream(currNode.sequent().succedent().spliterator(),
                                true)
                        .map(sf -> JavaTools.getActiveStatement(TermBuilder
                                .goBelowUpdates(sf.formula()).javaBlock()))
                        .filter(st -> st instanceof While).map(st -> (While) st)
                        .findAny();

                assert maybeWhile.isPresent() : ""
                        + "There has to be a while loop "
                        + "somewhere at this node.";

                List<LocationVariable> lLocalOuts = null;
                Term lLoopInvTerm = null;

                try {
                    final LoopInvariantInformation loopInvInf = //
                            LoopScopeInvariantRule.INSTANCE.doPreparations( //
                                    currNode, services,
                                    currNode.getAppliedRuleApp());

                    lLoopInvTerm = loopInvInf.invTerm;
                    lLocalOuts = StreamSupport
                            .stream(loopInvInf.inst.inv.getLocalOuts()
                                    .spliterator(), true)
                            .map(t -> (LocationVariable) t.op())
                            .collect(Collectors.toList());
                } catch (RuleAbortException e) {
                    throw new RuntimeException(String.format(
                            "%s: Problem in instantiating rule app: %s",
                            this.getClass().getSimpleName(), e.getMessage()),
                            e);
                }

                return new AnalyzeInvImpliesLoopEffectsRuleApp(this.builtInRule,
                        this.pio, lLoopInvTerm, lLocalOuts);

            }

            currNode = currNode.parent();
        }

        return null;
    }

    public Term getInvTerm() {
        return invTerm;
    }

    public List<LocationVariable> getLocalOuts() {
        return localOuts;
    }

}
