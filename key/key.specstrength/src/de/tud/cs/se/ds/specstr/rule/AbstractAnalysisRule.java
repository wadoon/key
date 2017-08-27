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
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * An abstract {@link BuiltInRule} for strength analysis.
 *
 * @author Dominic Steinhoefel
 */
public abstract class AbstractAnalysisRule implements BuiltInRule {

    /**
     * The {@link Proof} branch label for a strength analysis case showing that
     * a loop invariant is preserved.
     */
    public static final String INVARIANT_PRESERVED_BRANCH_LABEL = "Invariant preserved";

    /**
     * The {@link Proof} branch label for a strength analysis case showing that
     * a post condition is satisfied.
     */
    public static final String POSTCONDITION_SATISFIED_BRANCH_LABEL = "Postcondition satisfied";

    /**
     * The {@link Proof} branch label prefix for fact coverage branches.
     */
    public static final String COVERS_FACT_BRANCH_LABEL_PREFIX = "Covers fact";

    /**
     * A hint for term label refactoring; indicates that a term is a fact of an
     * analysis.
     */
    public static final String FACT_HINT = "factToAnalyze";

    /**
     * A hint for term label refactoring; indicates that a term is the premise
     * used to show coverage of a fact.
     */
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
     * Checks whether the given {@link Node} is already a child of an analysis
     * case. In the worst case, this method iterates all the way to the root of
     * a {@link Proof}.
     *
     * @param n
     *            The {@link Node} to check.
     * @return true iff the given {@link Node} is the child of an analysis case.
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
     * If the given {@link Node} is in the subtree of an analysis case, the rule
     * for that case is returned; otherwise an empty {@link Optional}.
     *
     * @param n
     *            The {@link Node} to check.
     * @return Either the {@link AbstractAnalysisRule} in the scope of which the
     *         given {@link Node} resides, or an empty {@link Optional}.
     */
    public static Optional<RuleApp> analysisRuleAppOfThisScope(Node n) {
        if (n.getAppliedRuleApp().rule() instanceof AbstractAnalysisRule) {
            return Optional.of(n.getAppliedRuleApp());
        }

        if (n.root()) {
            return Optional.empty();
        }

        return analysisRuleAppOfThisScope(n.parent());
    }

}
