package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.IntCaseDistinctionRule;

import javax.swing.*;

/**
 * @author Alexander Weigl
 * @version 1 (6/3/21)
 */
public class IntCaseDistinctionCompletion implements InteractiveRuleApplicationCompletion {
    private final MainWindow window;

    public IntCaseDistinctionCompletion(MainWindow mainWindow) {
        this.window = mainWindow;
    }

    @Override
    public IBuiltInRuleApp complete(IBuiltInRuleApp app, Goal goal, boolean forced) {
        IntCaseDistinctionRule.IntCaseDistinctionRuleApp ruleApp =
                (IntCaseDistinctionRule.IntCaseDistinctionRuleApp) app;

        int lower = getIntegerValue("Select lower bound", "0");
        int upper = getIntegerValue("Select upper bound", "16");
        ruleApp.setRange(lower, upper);
        return app;
    }


    private int getIntegerValue(String s, String s2) {
        int lower;
        while (true) {
            try {
                String slower = JOptionPane.showInputDialog(window, s, s2);
                lower = Integer.parseInt(slower);
                break;
            } catch (NumberFormatException ignore) {
            }
        }
        return lower;
    }


    @Override
    public boolean canComplete(IBuiltInRuleApp app) {
        return app instanceof IntCaseDistinctionRule.IntCaseDistinctionRuleApp;
    }
}
