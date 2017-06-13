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

import java.util.Optional;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.BuiltInRule;

/**
 * TODO Comment.
 *
 * @author Dominic Steinhöfel
 */
public abstract class AbstractAnalysisRule implements BuiltInRule {

    public static final String INVARIANT_PRESERVED_BRANCH_LABEL = "Invariant preserved";
    public static final String POSTCONDITION_SATISFIED_BRANCH_LABEL = "Postcondition satisfied";
    public static final String COVERS_FACT_BRANCH_LABEL_PREFIX = "Covers fact";
    public static final String FACT_HINT = "factToAnalyze";
    public static final Object FACT_PREMISE_HINT = "factPremiseHint";

    /**
     * @return true iff the {@link FactAnalysisRule} should add a goal where all
     *         loop invariant facts are removed.
     */
    public abstract boolean addCoveredWithoutLoopInvGoal();

    /**
     * @return true iff the {@link FactAnalysisRule} should add a goal where the
     *         fact and the premise are swapped, i.e., the fact is "abstractly
     *         covered" by the specification.
     */
    public abstract boolean addAbstractlyCoveredGoal();

    /**
     * TODO
     * 
     * @param n
     * @return
     */
    public static boolean alreadyAnalysisGoal(Node n) {
        if (n.getAppliedRuleApp().rule() instanceof AbstractAnalysisRule) {
            return true;
        }

        if (n.root()) {
            return false;
        }

        return alreadyAnalysisGoal(n.parent());
    }
    
    /**
     * TODO Comment.
     *
     * @param n
     * @return
     */
    public static Optional<AbstractAnalysisRule> analysisRuleOfThisScope(Node n) {
        if (n.getAppliedRuleApp().rule() instanceof AbstractAnalysisRule) {
            return Optional.of((AbstractAnalysisRule) n.getAppliedRuleApp().rule());
        }

        if (n.root()) {
            return Optional.empty();
        }
        
        return analysisRuleOfThisScope(n.parent());
    }

}
