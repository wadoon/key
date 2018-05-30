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

package de.uka.ilkd.key.strategy;

/**
 * Singleton implementation of the <code>RuleAppCost</code> interface, which
 * denotes a maximum cost (rule applications with this cost can't be afforded
 * at all)
 * <p>
 * History:
 * <ul>
 * <li>weigl: reformated, cleanup (delete hashCode, equals Method)</li>
 * </ul>
 */
public class TopRuleAppCost implements RuleAppCost {
    /**
     * Singleton Instance.
     */
    public static final TopRuleAppCost INSTANCE = new TopRuleAppCost();

    private TopRuleAppCost() {
    }

    @Override
    public int compareTo(RuleAppCost o) {
        if (o instanceof TopRuleAppCost)
            return 0;
        return 1;
    }

    @Override
    public final RuleAppCost add(RuleAppCost cost2) {
        return INSTANCE;
    }

    @Override
    public RuleAppCost mul(RuleAppCost cost) {
        return INSTANCE;
    }

    @Override
    public String toString() {
        return "Costs infinite";
    }
}