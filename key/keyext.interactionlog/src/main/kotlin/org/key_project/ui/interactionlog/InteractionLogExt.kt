package org.key_project.ui.interactionlog

import bibliothek.gui.dock.common.CLocation
import bibliothek.gui.dock.common.SingleCDockable
import de.uka.ilkd.key.core.KeYSelectionEvent
import de.uka.ilkd.key.core.KeYSelectionListener
import de.uka.ilkd.key.gui.MainWindow
import de.uka.ilkd.key.gui.actions.KeyAction
import de.uka.ilkd.key.gui.actions.MainWindowAction
import de.uka.ilkd.key.gui.docking.DockingHelper
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension
import de.uka.ilkd.key.gui.fonticons.IconFactory
import org.key_project.ui.BoundsPopupMenuListener
import org.key_project.ui.interactionlog.api.InteractionRecorderListener
import org.key_project.ui.interactionlog.model.InteractionLog
import java.awt.Component
import java.awt.event.ActionEvent
import java.util.*
import javax.swing.*
import javax.swing.filechooser.FileNameExtensionFilter

/**
 * @author Alexander Weigl
 * @version 1 (13.02.19)
 */
@KeYGuiExtension.Info(name = "Interaction Logging", optional = true, experimental = true, priority = 10000)
class InteractionLogExt : KeYGuiExtension, KeYGuiExtension.MainMenu, KeYGuiExtension.Toolbar, InteractionRecorderListener {
    companion object {
        val recorder = InteractionRecorder()

        fun disableLogging() {
            recorder.isDisableAll = true
        }

        fun enableLogging() {
            recorder.isDisableAll = false
        }
    }

    private var toolbar = JToolBar("interaction logging")
    private val interactionLogSelection = JComboBox<InteractionLog>()

    init {
        val listener = BoundsPopupMenuListener(true, false)

        interactionLogSelection.renderer = object : DefaultListCellRenderer() {
            override fun getListCellRendererComponent(list: JList<*>?, value: Any?, index: Int, isSelected: Boolean, cellHasFocus: Boolean): Component {
                val v = value ?: "No log loaded."
                return super.getListCellRendererComponent(list, v, index, isSelected, cellHasFocus)
            }
        }

        interactionLogSelection.addPopupMenuListener(listener)
        interactionLogSelection.prototypeDisplayValue = InteractionLog("12345678901234567890")

        toolbar.add(LoadAction())
        toolbar.add(PauseLoggingAction())
        toolbar.add(interactionLogSelection)


        recorder.addListener(object : InteractionRecorderListener {
            override fun onNewInteractionLog(recorder: InteractionRecorder, log: InteractionLog) {
                interactionLogSelection.addItem(log)
                println(log)
            }

            override fun onDisposeInteractionLog(recorder: InteractionRecorder, log: InteractionLog) {
                interactionLogSelection.removeItem(log)
            }
        })
    }


    override fun getToolbar(mainWindow: MainWindow): JToolBar {
        mainWindow.userInterface.proofControl.addInteractionListener(recorder)
        mainWindow.userInterface.proofControl.addAutoModeListener(recorder)
        mainWindow.mediator.addKeYSelectionListener(object : KeYSelectionListener {
            override fun selectedNodeChanged(e: KeYSelectionEvent?) {}

            override fun selectedProofChanged(e: KeYSelectionEvent?) {
                recorder.get(mainWindow.mediator.selectedProof)
            }
        })
        toolbar.add(ShowLogAction(mainWindow))
        return toolbar
    }

    override fun getMainMenuActions(mainWindow: MainWindow): List<Action> {
        return Arrays.asList(
                /*ilv.actionAddUserNote,
                ilv.actionExportMarkdown,
                ilv.actionJumpIntoTree,
                ilv.actionLoad,
                ilv.actionSave,
                ilv.actionTryReapply,
                ilv.actionKPSExport,
                ilv.actionToggleFavourite,
                ilv.actionExportMarkdown,
                ilv.actionMUCopyClipboard,
                ilv.actionPauseLogging*/)
    }


    private inner class PauseLoggingAction : KeyAction() {
        init {
            isSelected = InteractionLogExt.recorder.isDisableAll
            priority = -1
            menuPath = InteractionLogView.MENU_ILOG
            putValue(Action.SHORT_DESCRIPTION, "Activation or Deactivation of interaction logging")

            update()
            addPropertyChangeListener { evt ->
                if (evt.propertyName == Action.SELECTED_KEY)
                    update()
            }
            lookupAcceleratorKey()
        }

        private fun update() {
            if (!isSelected) {
                setIcon(IconFactory.INTERLOG_PAUSE.get())
                name = "Pause Interaction Logging"
            } else {
                setIcon(IconFactory.INTERLOG_RESUME.get())
                name = "Resume Interaction Logging"
            }
        }

        override fun actionPerformed(e: ActionEvent) {
            isSelected = !isSelected
            InteractionLogExt.recorder.isDisableAll = isSelected
        }
    }


    private inner class LoadAction internal constructor() : KeyAction() {
        init {
            name = "Load"
            putValue(Action.SHORT_DESCRIPTION, "Load Interaction Log")
            setIcon(InteractionLogView.ICON_LOAD.get(InteractionLogView.SMALL_ICON_SIZE))
            priority = 0
            menuPath = InteractionLogView.MENU_ILOG
            lookupAcceleratorKey()
        }

        override fun actionPerformed(e: ActionEvent) {
            val fileChooser = JFileChooser()
            fileChooser.fileFilter = FileNameExtensionFilter(
                    "InteractionLog", "xml")
            val returnValue = fileChooser.showOpenDialog(null)
            if (returnValue == JFileChooser.APPROVE_OPTION) {
                try {
                    val file = fileChooser.selectedFile
                    recorder.readInteractionLog(file)
                    //addInteractionLog(importedLog);
                } catch (exception: Exception) {
                    JOptionPane.showMessageDialog(null,
                            exception.cause,
                            "IOException",
                            JOptionPane.WARNING_MESSAGE)
                    exception.printStackTrace()
                }

            }
        }
    }


    private inner class ShowLogAction(window: MainWindow) : MainWindowAction(window) {
        init {
            name = "Load"
            tooltip = "Show the interaction log"
            smallIcon = InteractionLogView.ICON_SHOW.get(InteractionLogView.SMALL_ICON_SIZE)
            priority = 0
            menuPath = InteractionLogView.MENU_ILOG
            lookupAcceleratorKey()
        }

        override fun actionPerformed(e: ActionEvent?) {
            showLog()
        }

        private val map = HashMap<InteractionLog, InteractionLogView>()

        private fun showLog(log: InteractionLog? = null) {
            val l = log ?: interactionLogSelection.selectedItem as? InteractionLog
            if (l != null) {
                val view = map.computeIfAbsent(l) {
                    InteractionLogView(l, mainWindow.mediator)
                }
                mainWindow.dockControl.addDockable(view.dockable)
                view.dockable.isVisible = true
                view.dockable.setLocation(CLocation.base().normalEast(.3))
            } else {
                mainWindow.setStatusLine("No interaction is loaded or selected.")
            }
        }
    }
}

