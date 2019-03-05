package edu.key_project.script.ui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ext.KeYMainMenuExtension;
import de.uka.ilkd.key.gui.ext.KeYPaneExtension;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeBold;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import lombok.Getter;

import javax.swing.*;
import java.util.Arrays;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (01.03.19)
 */
public class UIScriptExtension implements KeYPaneExtension, KeYMainMenuExtension {
    @Getter
    private static ScriptPanel panel;
    @Getter
    private static Actions actions;

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        if (panel == null)
            panel = new ScriptPanel(window, mediator);
        if (actions == null)
            actions = new Actions(window, mediator);
    }

    @Override
    public String getTitle() {
        return "Scripts";
    }

    @Override
    public Icon getIcon() {
        return IconFontSwing.buildIcon(FontAwesomeBold.PEN, 16);
    }

    @Override
    public JComponent getComponent() {
        return panel;
    }

    @Override
    public int priority() {
        return 1500;
    }

    @Override
    public List<Action> getMainMenuActions(MainWindow mainWindow) {
        init(mainWindow, mainWindow.getMediator());
        return Arrays.asList(
                panel.getActionExecute(),
                panel.getActionLoad(),
                panel.getActionSave(),
                panel.getActionSaveAs(),
                panel.getActionCasesFromGoals(),
                panel.getActionSimpleReformat(),
                panel.getActionToggleAction(),
                panel.getActionStop(),
                panel.getActionStepOver(),
                panel.getActionContinue(),
                actions.getCopyNodePathBranchLabelsAction(),
                actions.getCopyNodePathLineNumbersAction(),
                actions.getCopyNodePathProgramStatementsAction(),
                actions.getCopyNodePathRuleNamesAction()
        );
    }

}
