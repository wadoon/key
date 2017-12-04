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

package de.uka.ilkd.key.macros;

import java.util.Set;

/**
 * The macro ExpandAndRightMacro applies rules to decompose propositional
 * toplevel formulas; it is used to decompose conjunctively connected proof
 * obligations on the right.
 *
 * The rules that are applied can be set in {@link #ADMITTED_RULES}.
 *
 * @author mattias ulbrich
 */
public class ExpandAndRightMacro extends AbstractPropositionalExpansionMacro {

    @Override
    public String getName() {
        return "Propositional expansion (w/ splits)";
    }

    @Override
    public String getDescription() {
        return "Apply rules to decompose propositional toplevel formulas; " +
                "splits the goal if necessary";
    }

    @Override
    public String getScriptCommandName() {
        return "split-prop";
    }

    private static final String[] ADMITTED_RULES = {
        "andLeft", "orRight", "impRight", "andRight",
        "closeTrue", "closeFalse", "true_left", "false_right",
    };

    private static final Set<String> ADMITTED_RULES_SET = asSet(ADMITTED_RULES);

    @Override
    protected Set<String> getAdmittedRuleNames() {
        return ADMITTED_RULES_SET;
    }

    @Override
    protected boolean allowOSS() {
        return false;
    }
}