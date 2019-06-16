package org.key_project.ui.interactionlog

import de.uka.ilkd.key.core.KeYMediator
import de.uka.ilkd.key.core.KeYSelectionEvent
import de.uka.ilkd.key.core.KeYSelectionListener
import de.uka.ilkd.key.gui.MainWindow
import de.uka.ilkd.key.gui.actions.KeyAction
import de.uka.ilkd.key.gui.extension.api.TabPanel
import de.uka.ilkd.key.gui.fonticons.FontAwesomeRegular
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid
import de.uka.ilkd.key.gui.fonticons.IconFactory
import de.uka.ilkd.key.gui.fonticons.IconFontProvider
import de.uka.ilkd.key.proof.Proof
import org.key_project.ui.BoundsPopupMenuListener
import org.key_project.ui.interactionlog.algo.MUProofScriptExport
import org.key_project.ui.interactionlog.algo.MarkdownExport
import org.key_project.ui.interactionlog.api.Interaction
import org.key_project.ui.interactionlog.model.InteractionLog
import org.key_project.ui.interactionlog.api.InteractionRecorderListener
import org.key_project.ui.interactionlog.model.NodeInteraction
import org.key_project.ui.interactionlog.model.UserNoteInteraction
import java.awt.*
import java.awt.datatransfer.DataFlavor
import java.awt.datatransfer.StringSelection
import java.awt.datatransfer.UnsupportedFlavorException
import java.awt.dnd.DropTarget
import java.awt.dnd.DropTargetAdapter
import java.awt.dnd.DropTargetDropEvent
import java.awt.event.*
import java.io.File
import java.io.FileWriter
import java.io.IOException
import java.io.PrintWriter
import java.text.SimpleDateFormat
import java.util.*
import javax.swing.*
import javax.swing.border.Border
import javax.swing.filechooser.FileNameExtensionFilter

class InteractionLogView(window: MainWindow, mediator: KeYMediator) : JPanel(), InteractionRecorderListener, TabPanel {
    val recorder = InteractionRecorder()

    val actionExportProofScript: KeyAction = ExportMUScriptAction()
    val actionKPSExport: KeyAction = ExportKPSAction()
    val actionSave: KeyAction = SaveAction()
    val actionLoad: KeyAction = LoadAction()
    val actionAddUserNote: KeyAction = AddUserNoteAction()
    val actionToggleFavourite: KeyAction = ToggleFavouriteAction()
    val actionJumpIntoTree: KeyAction = JumpIntoTreeAction()
    val actionTryReapply: KeyAction = TryReapplyAction()
    val actionExportMarkdown: KeyAction = ExportMarkdownAction()
    val actionShowExtended: KeyAction = ShowExtendedActionsAction()
    val actionMUCopyClipboard: KeyAction = ExportMUScriptClipboardAction()
    val actionPauseLogging: KeyAction = PauseLoggingAction()


    val listInteraction = JList<Interaction>()
    val interactionLogSelection = JComboBox<InteractionLog>()
    val interactionListModel = DefaultListModel<Interaction>()
    private var mediator: KeYMediator? = null
    private var currentProof: Proof? = null
    private val keYSelectionListener = object : KeYSelectionListener {
        override fun selectedNodeChanged(e: KeYSelectionEvent) {}

        override fun selectedProofChanged(e: KeYSelectionEvent) {
            setCurrentProof(e.source.selectedProof)
        }
    }
    private var fileChooser: JFileChooser = JFileChooser()

    private val selectedItem: InteractionLog
        get() = interactionLogSelection.getSelectedItem() as InteractionLog

    init {
        // register the recorder in the proof control
        listInteraction.model = interactionListModel
        listInteraction.cellRenderer = InteractionCellRenderer()

        val listener = BoundsPopupMenuListener(true, false)
        interactionLogSelection.addPopupMenuListener(listener)
        interactionLogSelection.prototypeDisplayValue = InteractionLog("INTERACTION LOG")


        val panelButtons = JToolBar()
        panelButtons.add(interactionLogSelection)
        val btnLoad = JButton(actionLoad)
        val btnSave = JButton(actionSave)
        val btnExport = JButton(actionExportProofScript)
        val btnAddNote = JButton(actionAddUserNote)

        btnExport.hideActionText = true
        btnSave.hideActionText = true
        btnAddNote.hideActionText = true
        btnLoad.hideActionText = true

        panelButtons.add(btnLoad)
        panelButtons.add(btnSave)
        panelButtons.add(Box.createHorizontalGlue())
        panelButtons.add(actionAddUserNote)
        panelButtons.addSeparator()
        panelButtons.add(actionShowExtended)

        val popup = JPopupMenu()
        popup.add(JMenuItem(actionMUCopyClipboard))
        popup.addSeparator()
        popup.add(JMenuItem(actionToggleFavourite))
        popup.add(JMenuItem(actionJumpIntoTree))
        popup.add(JMenuItem(actionTryReapply))
        popup.addSeparator()
        popup.add(JMenuItem(actionAddUserNote))
        listInteraction.componentPopupMenu = popup

        recorder.addListener(this)

        interactionLogSelection.model = recorder.getLoadedInteractionLogs()
        interactionLogSelection.addActionListener { this.handleSelectionChange(it) }
        interactionLogSelection.model = recorder.getLoadedInteractionLogs()

        listInteraction.addMouseMotionListener(object : MouseMotionAdapter() {
            override fun mouseMoved(e: MouseEvent?) {
                val l = e!!.source as JList<*>
                val m = l.model
                val index = l.locationToIndex(e.point)
                if (index > -1) {
                    val inter = m.getElementAt(index) as Interaction
                    l.toolTipText = "<html>" + MarkdownExport.getHtml(inter) + "</html>"
                }
            }
        })

        interactionLogSelection.model = recorder.getLoadedInteractionLogs()

        DropTarget(listInteraction, 0, object : DropTargetAdapter() {
            override fun drop(dtde: DropTargetDropEvent) {
                val tr = dtde.transferable
                try {
                    val textFlavour = tr.getTransferData(DataFlavor.stringFlavor)
                    dtde.acceptDrop(dtde.dropAction)
                    dtde.dropComplete(true)
                    SwingUtilities.invokeLater { (actionAddUserNote as AddUserNoteAction).doAddNote(textFlavour.toString()) }
                    return
                } catch (e: UnsupportedFlavorException) {
                    e.printStackTrace()
                } catch (e: IOException) {
                    e.printStackTrace()
                }

                dtde.rejectDrop()
            }
        })

        layout = BorderLayout()
        add(panelButtons, BorderLayout.NORTH)
        add(JScrollPane(listInteraction))
        recorder.addListener(this)

        border = BorderFactory.createTitledBorder("Interactions")

        setMainWindow(window)
        setMediator(mediator)
    }

    private fun handleSelectionChange(actionEvent: ActionEvent) {
        val selectedLog = selectedItem
        updateList(selectedLog)
    }

    private fun setCurrentProof(proof: Proof?) {
        if (proof == null) return
        currentProof = proof
        recorder.get(proof)
        //rebuildList();
    }

    private fun rebuildList() {
        //val currentInteractionLog = selectedItem
        currentProof?.also {
            val state = recorder.get(it)
            updateList(state)
        }
    }

    private fun updateList(interactionLog: InteractionLog) {
        interactionListModel.clear()
        interactionLog.interactions.forEach { interactionListModel.addElement(it) }
    }

    private fun getFileChooser(): JFileChooser {
        if (currentProof != null) {
            val file = currentProof!!.proofFile
            if (file != null)
                fileChooser.currentDirectory = file.parentFile
        }
        return fileChooser
    }

    override fun onInteraction(interaction: Interaction) {
        rebuildList()
    }

    fun setMediator(mediator: KeYMediator) {
        if (this.mediator != null) {
            this.mediator!!.removeKeYSelectionListener(keYSelectionListener)
        }
        this.mediator = mediator
        mediator.addKeYSelectionListener(keYSelectionListener)
        setCurrentProof(mediator.selectedProof)
    }

    fun setMainWindow(window: MainWindow) {
        window.userInterface.proofControl.addInteractionListener(recorder)
        window.userInterface.proofControl.addAutoModeListener(recorder)
    }


    override fun getTitle(): String {
        return "Interaction Log"
    }

    override fun getIcon(): Icon? {
        return INTERACTION_LOG_ICON
    }

    override fun getComponent(): JComponent {
        return this
    }


    private inner class InteractionLogModelItem : DefaultComboBoxModel<InteractionLog>()

    private inner class ExportMUScriptAction internal constructor() : AbstractFileSaveAction() {
        init {
            name = "Export as Proof Script"
            setIcon(IconFactory.EXPORT_MU_SCRIPT.get())
            menuPath = MENU_ILOG_EXPORT
            lookupAcceleratorKey()
        }

        override fun save(selectedFile: File) {
            val current = selectedItem
            val script = MUProofScriptExport.getScript(current)
            try {
                FileWriter(selectedFile).use { fw -> fw.write(script) }
            } catch (e: IOException) {
                e.printStackTrace()
            }

        }
    }

    private inner class ExportMUScriptClipboardAction internal constructor() : KeyAction() {
        init {
            name = "Copy MUScript"
            smallIcon = IconFactory.EXPORT_MU_SCRIPT_CLIPBOARD.get()
            menuPath = MENU_ILOG_EXPORT
            lookupAcceleratorKey()
        }

        override fun actionPerformed(e: ActionEvent) {
            val text = (listInteraction.getSelectedValue() as Interaction).proofScriptRepresentation
            val clipboard = Toolkit.getDefaultToolkit().systemClipboard
            val contents = StringSelection(text)
            clipboard.setContents(contents, contents)
        }
    }

    private inner class LoadAction internal constructor() : KeyAction() {
        init {
            name = "Load"
            putValue(Action.SHORT_DESCRIPTION, "Load Interaction Log")
            setIcon(ICON_LOAD.get(SMALL_ICON_SIZE))
            priority = 0
            menuPath = MENU_ILOG
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

    private inner class SaveAction internal constructor() : KeyAction() {
        init {
            name = "Save"
            setIcon(IconFactory.INTERLOG_SAVE.get())
            menuPath = MENU_ILOG
            priority = 1
            lookupAcceleratorKey()
            //new ImageIcon(getClass().getResource("/de/uka/ilkd/key/gui/icons/database_save.png")));
        }


        override fun actionPerformed(e: ActionEvent) {
            val fileChooser = getFileChooser()
            val returnValue = fileChooser.showSaveDialog(null)
            if (returnValue == JFileChooser.APPROVE_OPTION) {
                val activeInteractionLog = selectedItem
                try {
                    InteractionLogFacade.storeInteractionLog(activeInteractionLog,
                            fileChooser.selectedFile)
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

    private inner class AddUserNoteAction internal constructor() : KeyAction() {
        init {
            name = "Add Note"
            setIcon(ICON_ADD_USER_ACTION.get(SMALL_ICON_SIZE))
            //new ImageIcon(getClass().getResource("/de/uka/ilkd/key/gui/icons/book_add.png")));
            menuPath = MENU_ILOG
            lookupAcceleratorKey()
        }

        override fun actionPerformed(e: ActionEvent) {
            doAddNote("")
        }

        internal fun doAddNote(prefilled: String) {
            val note = MultiLineInputPrompt(this@InteractionLogView, prefilled).show()
            if (note.isPresent) {
                val interaction = UserNoteInteraction(note.get())
                val interactionLog = interactionLogSelection.selectedItem as InteractionLog
                interactionLog.interactions.add(interaction)
                onInteraction(interaction)
            }

        }
    }

    private inner class ToggleFavouriteAction internal constructor() : KeyAction() {
        init {
            name = "Toggle Fav"
            putValue(Action.MNEMONIC_KEY, KeyEvent.VK_F)
            putValue(Action.ACCELERATOR_KEY, KeyStroke.getKeyStroke(KeyEvent.VK_M, InputEvent.CTRL_DOWN_MASK))
            setIcon(ICON_TOGGLE_FAVOURITE.get(SMALL_ICON_SIZE))
            menuPath = MENU_ILOG
            lookupAcceleratorKey()
        }

        override fun actionPerformed(e: ActionEvent) {
            if (listInteraction.getSelectedValue() != null) {
                listInteraction.getSelectedValue().isFavoured = !listInteraction.getSelectedValue().isFavoured
            }
        }
    }

    private inner class JumpIntoTreeAction internal constructor() : KeyAction() {
        init {
            name = "Jump into tree"
            putValue(Action.SMALL_ICON, IconFactory.JUMP_INTO_TREE.get())
            menuPath = MENU_ILOG
            lookupAcceleratorKey()
        }

        override fun actionPerformed(e: ActionEvent) {
            try {
                val current = listInteraction.selectedValue as? NodeInteraction
                if (current != null) {
                    val node = current.getNode(mediator!!.selectedProof)
                    mediator!!.selectionModel.selectedNode = node
                }
            } catch (ex: ClassCastException) {

            }

        }
    }

    private inner class TryReapplyAction internal constructor() : KeyAction() {
        init {
            putValue(Action.NAME, "Re-apply action")
            putValue(Action.SMALL_ICON, IconFactory.INTERLOG_TRY_APPLY.get())
            menuPath = MENU_ILOG
            lookupAcceleratorKey()
        }

        override fun actionPerformed(e: ActionEvent) {
            val inter = listInteraction.getSelectedValue()
            try {
                //Reapplication should be ignored by the logging.
                recorder.isDisableAll = true
                inter.reapply(mediator!!.ui, mediator!!.selectedGoal)
            } catch (ex: UnsupportedOperationException) {
                JOptionPane.showMessageDialog(null,
                        String.format("<html>Reapplication of %s is not implemented<br>If you know how to do it, then override the corresponding method in %s.</html>",
                                inter.javaClass), "A very expected error.", JOptionPane.ERROR_MESSAGE)
            } catch (e1: Exception) {
                e1.printStackTrace()
            } finally {
                recorder.isDisableAll = false
            }
        }
    }

    private abstract inner class AbstractFileSaveAction : KeyAction() {

        override fun actionPerformed(e: ActionEvent) {
            val fc = getFileChooser()
            val choice = fc.showSaveDialog(e.source as Component)
            if (choice == JFileChooser.APPROVE_OPTION) {
                save(fc.selectedFile)
            }
        }

        internal abstract fun save(selectedFile: File)
    }

    private inner class ExportKPSAction : AbstractFileSaveAction() {
        init {
            name = "Export as KPS …"
            putValue(Action.SHORT_DESCRIPTION, "Export the current log into the KPS format.")
            setIcon(IconFactory.INTERLOG_EXPORT_KPS.get())
            menuPath = MENU_ILOG_EXPORT
            lookupAcceleratorKey()
        }

        override fun save(selectedFile: File) {
            try {
                FileWriter(selectedFile).use { fw -> MarkdownExport.writeTo(selectedItem, PrintWriter(fw)) }
            } catch (e: IOException) {
                e.printStackTrace()
            }

        }
    }

    private inner class ExportMarkdownAction : AbstractFileSaveAction() {
        init {
            name = "Export as markdown …"
            putValue(Action.SHORT_DESCRIPTION, "Export the current log into a markdown file.")
            setIcon(ICON_MARKDOWN.get(SMALL_ICON_SIZE))
            menuPath = MENU_ILOG_EXPORT
            lookupAcceleratorKey()
        }

        override fun save(selectedFile: File) {
            try {
                FileWriter(selectedFile).use { fw -> MarkdownExport.writeTo(selectedItem, PrintWriter(fw)) }
            } catch (e: IOException) {
                e.printStackTrace()
            }

        }
    }

    private inner class ShowExtendedActionsAction : KeyAction() {
        init {
            name = "More …"
            putValue(Action.SHORT_DESCRIPTION, "Shows further options")
            setIcon(IconFactory.INTERLOW_EXTENDED_ACTIONS.get())
            lookupAcceleratorKey()
        }

        fun createMenu(): JPopupMenu {
            val menu = JPopupMenu(name)
            menu.add(actionExportMarkdown)
            menu.add(actionExportProofScript)
            menu.add(actionKPSExport)
            return menu
        }

        override fun actionPerformed(e: ActionEvent) {
            val btn = e.source as JComponent
            val menu = createMenu()
            //val pi = MouseInfo.getPointerInfo()
            menu.show(btn, 0, 0)
            //pi.getLocation().x, pi.getLocation().y);
        }
    }

    private inner class PauseLoggingAction : KeyAction() {
        init {
            isSelected = recorder.isDisableAll
            priority = -1
            menuPath = MENU_ILOG
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
            setSelected(!isSelected)
            recorder.isDisableAll = isSelected
        }
    }

    companion object {
        private val INTERACTION_LOG_ICON = IconFactory.INTERLOG_ICON.get()
        private val SMALL_ICON_SIZE = 16f
        private val MENU_ILOG = "Interaction Logging"
        private val MENU_ILOG_EXPORT = "$MENU_ILOG.Export"

        private val ICON_LOAD = IconFontProvider(FontAwesomeSolid.TRUCK_LOADING)
        private val ICON_ADD_USER_ACTION = IconFontProvider(FontAwesomeRegular.STICKY_NOTE)
        private val ICON_TOGGLE_FAVOURITE = IconFontProvider(FontAwesomeSolid.HEART, Color.red)
        private val ICON_MARKDOWN = IconFontProvider(FontAwesomeSolid.MARKDOWN)
    }
}

internal class MultiLineInputPrompt(private var parent: JComponent?, private val text: String) {
    val dialog: JDialog by lazy {
        val d = JDialog(JOptionPane.getFrameForComponent(parent))
        d.isModal = true
        d.title = "Enter note..."

        val root = JPanel(BorderLayout(10, 10))
        val box = JPanel(FlowLayout(FlowLayout.CENTER))
        root.add(box, BorderLayout.SOUTH)
        val area = JTextArea(text)
        val btnOk = JButton("OK")
        val btnCancel = JButton("Cancel")
        box.add(btnOk)
        box.add(btnCancel)

        btnOk.addActionListener { evt -> accept(area.text) }
        btnCancel.addActionListener { evt -> cancel() }
        d.defaultCloseOperation = JDialog.HIDE_ON_CLOSE
        d.addWindowListener(object : WindowAdapter() {
            override fun windowClosed(e: WindowEvent?) {
                cancel()
            }
        })
        d.contentPane = root

        root.add(JScrollPane(area), BorderLayout.CENTER)
        d.setSize(300, 200)
        d.setLocationRelativeTo(parent)
        dialog
    }

    private var acceptedAnswer: String? = null

    private fun cancel() {
        acceptedAnswer = null
        dialog.isVisible = false
    }

    private fun accept(text: String) {
        acceptedAnswer = text
        dialog.isVisible = false
    }

    fun show(): Optional<String> {
        dialog.isVisible = true
        return Optional.ofNullable(acceptedAnswer)
    }

    fun setParent(parent: JComponent) {
        this.parent = parent
    }
}

internal class InteractionCellRenderer : JPanel(), ListCellRenderer<Interaction> {
    private val lblIconLeft = JLabel()
    private val lblIconRight = JLabel()
    private val lblText = JLabel()
    private val iconHeart = IconFactory.INTERLOG_TOGGLE_FAV.get()

    init {
        layout = BorderLayout()
        add(lblIconLeft, BorderLayout.WEST)
        add(lblIconRight, BorderLayout.EAST)
        add(lblText)
    }

    override fun getListCellRendererComponent(list: JList<out Interaction>, value: Interaction?, index: Int, isSelected: Boolean, cellHasFocus: Boolean): Component {
        lblText.text = if (value != null)
            df.format(value.created) + " " + value.toString()
        else
            ""
        lblIconRight.icon = if (value != null && value.isFavoured) iconHeart else null
        //TODO
        border = if (value != null && value.isFavoured) BorderFactory.createLineBorder(COLOR_FAVOURED) else null

        componentOrientation = list.componentOrientation

        if (isSelected) {
            background = list.selectionBackground
            foreground = list.selectionForeground
        } else {
            if (value != null) {
                background = if (value.graphicalStyle.backgroundColor != null)
                    value.graphicalStyle.backgroundColor
                else
                    list.background

                foreground = if (value.graphicalStyle.foregroundColor != null)
                    value.graphicalStyle.foregroundColor
                else
                    list.foreground
            }
        }

        lblIconRight.foreground = foreground
        lblIconLeft.foreground = foreground
        lblText.foreground = foreground

        lblIconRight.background = background
        lblIconLeft.background = background
        lblText.background = background


        isEnabled = list.isEnabled
        font = list.font

        var border: Border? = null
        if (cellHasFocus) {
            if (isSelected) {
                border = UIManager.getDefaults().getBorder("List.focusSelectedCellHighlightBorder")
            }
            if (border == null) {
                border = UIManager.getDefaults().getBorder("List.focusCellHighlightBorder")
            }
        } else {
        }
        return this
    }

    companion object {
        private val df = SimpleDateFormat("yyyy-MM-dd HH:mm:ss")
        private val COLOR_FAVOURED = Color(0xFFD373)
    }


}
