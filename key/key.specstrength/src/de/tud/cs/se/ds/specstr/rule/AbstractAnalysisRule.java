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

}
