package org.key_project.ui.interactionlog

import de.uka.ilkd.key.core.KeYMediator
import de.uka.ilkd.key.gui.MainWindow
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension
import de.uka.ilkd.key.gui.extension.api.TabPanel
import java.util.*
import javax.swing.Action

/**
 * @author Alexander Weigl
 * @version 1 (13.02.19)
 */
@KeYGuiExtension.Info(name = "Interaction Logging", optional = true, experimental = false, priority = 10000)
class InteractionLogExt : KeYGuiExtension, KeYGuiExtension.LeftPanel, KeYGuiExtension.MainMenu {
    private var interactionLogView: InteractionLogView? = null


    override fun getMainMenuActions(mainWindow: MainWindow): List<Action> {
        val ilv = getView(mainWindow)

        return Arrays.asList(
                ilv.actionAddUserNote,
                ilv.actionExportMarkdown,
                ilv.actionJumpIntoTree,
                ilv.actionLoad,
                ilv.actionSave,
                ilv.actionTryReapply,
                ilv.actionKPSExport,
                ilv.actionToggleFavourite,
                ilv.actionExportMarkdown,
                ilv.actionMUCopyClipboard,
                ilv.actionPauseLogging)
    }

    private fun getView(mainWindow: MainWindow): InteractionLogView {
        return interactionLogView ?: let {
            InteractionLogView(mainWindow, mainWindow.mediator)
                    .also { interactionLogView = it }
        }
    }

    override fun getPanels(window: MainWindow, mediator: KeYMediator): Collection<TabPanel> {
        return setOf<TabPanel>(getView(window))
    }
}
