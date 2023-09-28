/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.tucrule;

import de.uka.ilkd.key.gui.InteractiveRuleApplicationCompletion;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.tuc.TucRuleApp;

public class TucRuleCompletion implements InteractiveRuleApplicationCompletion {
    @Override
    public IBuiltInRuleApp complete(final IBuiltInRuleApp app, final Goal goal, final boolean forced) {
        return null;
    }

    @Override
    public boolean canComplete(final IBuiltInRuleApp app) {
        return app instanceof TucRuleApp;
    }
}
