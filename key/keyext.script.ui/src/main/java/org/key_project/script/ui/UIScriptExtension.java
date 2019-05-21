package org.key_project.script.ui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import edu.kit.iti.formal.psdbg.interpreter.dbg.DebuggerFramework;
import lombok.Getter;
import org.key_project.editor.EditorFacade;

import javax.swing.*;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (01.03.19)
 */
@KeYGuiExtension.Info(
        name = "Proof Scripting UI",
        disabled = false,
        priority = 1000,
        experimental = false)
public class UIScriptExtension implements
        KeYGuiExtension,
        KeYGuiExtension.LeftPanel,
        KeYGuiExtension.MainMenu,
        KeYGuiExtension.StatusLine
//        KeYGuiExtension.Toolbar
{
    static {
        ScriptUtils.registerCodeTemplates();
        ScriptUtils.registerKPSLanguage();
        EditorFacade.register(new ScriptEditorFactory());
    }

    private JLabel lblInterpreterStatus = new JLabel();


    @Getter
    private CommandHelpPane commandHelpPane;

    @Getter
    private Actions actions;

    public void init(MainWindow window, KeYMediator mediator) {
        if (commandHelpPane == null)
            commandHelpPane = new CommandHelpPane(window, mediator);
        if (actions == null)
            actions = new Actions(window, mediator);


        Timer timer = new Timer(100, e -> {
            DebuggerFramework<?> debuggerFramework = mediator.get(DebuggerFramework.class);
            boolean flag = debuggerFramework != null &&
                    debuggerFramework.getInterpreterThread() != null &&
                    (debuggerFramework.getInterpreterThread().getState() == Thread.State.WAITING
                            || debuggerFramework.getInterpreterThread().getState() == Thread.State.BLOCKED
                    );
            if (flag)
                mediator.startInterface(true);

            if (debuggerFramework != null && debuggerFramework.getInterpreterThread() != null)
                lblInterpreterStatus.setText(debuggerFramework.getInterpreterThread().getState().toString());
        });
    }

    @Override
    public List<Action> getMainMenuActions(MainWindow mainWindow) {
        init(mainWindow, mainWindow.getMediator());
        return Arrays.asList(
                /*panel.getActionExecute(),
                panel.getActionLoad(),
                panel.getActionSave(),
                panel.getActionSaveAs(),
                panel.getActionCasesFromGoals(),
                panel.getActionSimpleReformat(),
                panel.getActionToggleAction(),
                panel.getActionStop(),
                panel.getActionStepOver(),
                panel.getActionContinue(),*/
                actions.getCopyNodePathBranchLabelsAction(),
                actions.getCopyNodePathLineNumbersAction(),
                actions.getCopyNodePathProgramStatementsAction(),
                actions.getCopyNodePathRuleNamesAction()
        );
    }

    /*@Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        init(mainWindow,mainWindow.getMediator());
        JToolBar toolbar = new JToolBar("Script Execution");
        toolbar.add(panel.getActionLoad());
        toolbar.add(panel.getActionSave());
        toolbar.addSeparator();
        toolbar.add(panel.getActionExecute());
        toolbar.add(panel.getActionStop());
        toolbar.add(panel.getActionContinue());
        toolbar.add(panel.getActionStepOver());
        return toolbar;
    }
*/
    @Override
    public Collection<TabPanel> getPanels(MainWindow window, KeYMediator mediator) {
        init(window, mediator);
        return Arrays.asList(commandHelpPane);
    }

    @Override
    public List<JComponent> getStatusLineComponents() {
        return Collections.singletonList(lblInterpreterStatus);
    }
}
