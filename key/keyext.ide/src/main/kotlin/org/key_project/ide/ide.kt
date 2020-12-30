package org.key_project.ide

import javafx.beans.binding.Bindings
import javafx.beans.property.SimpleDoubleProperty
import javafx.beans.property.SimpleListProperty
import javafx.beans.property.SimpleObjectProperty
import javafx.collections.FXCollections
import javafx.collections.ListChangeListener
import javafx.event.Event
import javafx.event.EventHandler
import javafx.geometry.Dimension2D
import javafx.geometry.Orientation
import javafx.scene.Group
import javafx.scene.Node
import javafx.scene.Scene
import javafx.scene.control.*
import javafx.scene.layout.BorderPane
import javafx.scene.layout.HBox
import javafx.scene.layout.Priority
import javafx.scene.layout.Region
import javafx.stage.FileChooser
import tornadofx.View
import tornadofx.getValue
import tornadofx.setValue
import tornadofx.usePrefSize
import java.nio.file.Path
import java.nio.file.Paths
import kotlin.io.path.ExperimentalPathApi
import kotlin.io.path.readText
import kotlin.io.path.writeText

interface Controller {
    val ui: Node
}

interface TabbedPane {
    val tab: Tab
}


@OptIn(ExperimentalPathApi::class)
class MainScene(val context: Context) : View() {
    //region controllers
    val menu = IdeMenu(context)
    val fileNavigator = FileNavigator(context)
    val outline = FileOutline(context)
    //endregion

    override val root = BorderPane()
    val scene = Scene(root, 300.0, 300.0)
    val hSplit = SplitPane()
    val vSplit = SplitPane()

    val paneNavigation = MultiTabPane(Orientation.VERTICAL)
    val paneTool = MultiTabPane(Orientation.HORIZONTAL)

    val statusBar = StatusBar(context)
    val problems = IssueList(context)

    val openEditors = arrayListOf<Editor>()
    val editorTabPanes: List<TabPane>
        get() = hSplit.items.filterIsInstance<TabPane>()

    val currentEditorProperty = SimpleObjectProperty<Editor>(this, "currentEditor", null)
    var currentEditor by currentEditorProperty

    init {
        context.register(this)

        paneNavigation.orientation = Orientation.VERTICAL
        vSplit.orientation = Orientation.VERTICAL

        root.top = menu.ui
        root.bottom = statusBar.ui
        vSplit.items.setAll(hSplit, paneTool.ui)
        root.center = vSplit

        paneNavigation.tabs.setAll(outline.tab, fileNavigator.tab)

        hSplit.items.add(paneNavigation.ui)
        hSplit.items.addAll(editorTabPanes)

        //paneNavigation.ui.maxWidthProperty().bind(hSplit.widthProperty().multiply(0.25));

        val appData = context.get<ApplicationData>()
        fileNavigator.rootFile = Paths.get(appData.lastNavigatorPath)

        hSplit.items.add(createEditorTabPane())

        //paneTool.tabClosingPolicy = TabPane.TabClosingPolicy.ALL_TABS
        /*paneTool.tabs.addListener(ChangeListener({ _, _, _ ->
            vSplit.setDividerPosition(0,1)
        })*/

//        paneTool.ui.centerProperty().addListener()

        addToolPanel(problems)

        SplitPane.setResizableWithParent(paneTool.ui, false)
        SplitPane.setResizableWithParent(paneNavigation.ui, false)
    }

    private fun addToolPanel(tab: TabbedPane) {
        paneTool.tabs.add(tab.tab)
    }

    fun publishMessage(status: String, graphic: Node? = null) {
        statusBar.message = status
        statusBar.graphic = graphic
    }

    private fun createEditorTabPane(): TabPane = TabPane().also { tabPane ->
        tabPane.tabs.addListener(ListChangeListener { onHandleEmptyTabs(tabPane) })
    }

    fun createCodeEditor() {
        addEditorTab(Editor(context))
    }

    fun addEditorTab(editor: Editor) {
        val tabPanel = editorTabPanes.last()
        addEditorTab(editor, tabPanel)
    }

    fun addEditorTab(editor: Editor, tabPanel: TabPane) {
        val tab = Tab(editor.title.value, editor.ui)
        tab.onCloseRequest = EventHandler { evt -> onTabCloseRequest(evt, editor) }
        tabPanel.tabs.add(tab)
        editor.title.addListener { _, _, new -> tab.text = new }
        openEditors.add(editor)
        editor.ui.focusedProperty().addListener { obs, _, new -> if (new) currentEditor = editor }
        currentEditor = editor
        editor.ui.requestFocus()
    }

    private fun onTabCloseRequest(evt: Event, editor: Editor) {
        if (editor.dirty && !showTabCloseConfirmation()) {
            evt.consume()
        }
    }

    private fun showTabCloseConfirmation(): Boolean {
        val alert = Alert(Alert.AlertType.CONFIRMATION)
        alert.contentText = "Text is edited and not saved. Close anway?"
        val resp = alert.showAndWait()
        val cancel = resp.isEmpty || (resp.isPresent && resp.get() != ButtonType.OK)
        return !cancel
    }

    private fun onHandleEmptyTabs(tabPane: TabPane) {
        if (tabPane.tabs.isEmpty() && editorTabPanes.size > 2) {
            hSplit.items.remove(tabPane)
        }
    }

    fun closeEditorTab(editor: Editor? = currentEditor) {}


    /*fun close() {
        closeEditorTab()
    }*/

    fun exit() {
        scene.window.onCloseRequest
    }

    private fun onCloseRequest() {

    }

    fun saveAs(editor: Editor? = currentEditor) =
        editor?.also {
            val fileChooser = FileChooser()
            fileChooser.showSaveDialog(scene.window)?.let { new ->
                editor.filename = new.toPath()
                save(editor)
            }
        }

    fun save(editor: Editor? = currentEditor) {
        editor?.also { editor ->
            editor.filename?.also { filename ->
                filename.writeText(editor.editor.text)
            }
        }
    }

    fun open() {
        val fc = FileChooser()
        fc.showOpenDialog(scene.window)?.let { file ->
            open(file.toPath())
        }
    }

    val recentFiles get() = context.get<RecentFiles>().files

    fun open(f: Path) {
        if (f !in recentFiles) {
            recentFiles.add(f)
        }
        val editor = Editor(context)
        editor.filename = f
        editor.editor.insertText(0, f.readText())
        addEditorTab(editor)
    }

    fun addEditorTabPane(): TabPane {
        val oldDividers = hSplit.dividerPositions.copyOf(hSplit.dividerPositions.size + 1)
        val pane = createEditorTabPane().also { hSplit.items.add(it) }
        val newDividiers = hSplit.dividerPositions.copyOf()
        oldDividers[oldDividers.lastIndex] = newDividiers.last()
        hSplit.setDividerPositions(*oldDividers)
        return pane
    }

    fun editorToTheRight(editor: Editor? = currentEditor) {
        val (tabPane, tab) = getTabPane(editor)
        if (tabPane != null) {
            val tabIndex = editorTabPanes.indexOf(tabPane)
            if (tabPane == editorTabPanes.last()) {
                addEditorTabPane()
            }
            val target = editorTabPanes[tabIndex + 1]
            tabPane.tabs.remove(tab)
            target.tabs.add(tab)
        }
    }

    fun editorToTheLeft(editor: Editor? = currentEditor) {
        val (tabPane, tab) = getTabPane(editor)
        if (tabPane != null) {
            val tabIndex = editorTabPanes.indexOf(tabPane)
            if (tabPane == editorTabPanes.first()) {
                createEditorTabPane().also { hSplit.items.add(1, it) }
            }
            val target = editorTabPanes[tabIndex - 1]
            tabPane.tabs.remove(tab)
            target.tabs.add(tab)
        }
    }

    private fun getTabPane(editor: Editor?): Pair<TabPane?, Tab?> {
        editorTabPanes.forEach { pane ->
            pane.tabs.forEach { tab ->
                if (tab.content == editor?.ui) {
                    return pane to tab
                }
            }
        }
        return null to null
    }

    val currentFontSizeProperty = SimpleDoubleProperty(this, "currentFontSize", 12.0)
        .also {
            root.styleProperty().bind(Bindings.format("-fx-font-size: %.2fpt;", it));
        }
    var currentFontSize by currentFontSizeProperty

    fun increaseFontSize(step: Double = 2.0) {
        currentFontSize += step
    }

    fun decreaseFontSize(step: Double = 2.0) {
        currentFontSize -= step
    }
}

class StatusBar(context: Context) : Controller {
    val lblMessage = Label()
    val lblLineRow = Label()
    val lblError = Label()
    override val ui: HBox = HBox(10.0, lblMessage, lblLineRow, lblError)

    val messageProperty = lblMessage.textProperty()
    var message: String by messageProperty

    val graphicProperty = lblMessage.graphicProperty()
    var graphic by graphicProperty

    init {
        context.register<StatusBar>(this)
    }
}

class IdeMenu(val ctx: Context) {
    val file = Menu("File")
    val edit = Menu("Edit")
    val view = Menu("View")
    val tools = Menu("Tools")
    val recentFiles = Menu("Recent files")
    val ui = MenuBar(file, edit, view, tools)

    val main by ctx.ref<MainScene>()

    init {
        val rf = ctx.get<RecentFiles>().files
        rf.addListener(ListChangeListener { updateRecentFiles() })
        updateRecentFiles()

        val config = ctx.get<UserConfig>()

        val actionSaveAs = config.createItem("save-as") { main.saveAs() }
        val actionSave = config.createItem("save") { main.save() }
        val actionNew = config.createItem("new") { main.createCodeEditor() }
        val actionRun = config.createItem("run") { }
        val actionOpen = config.createItem("open") { main.open() }
        val actionClose = config.createItem("close") { main.close() }
        val actionIncrFontSize = config.createItem("incr-font-size") { main.increaseFontSize() }
        val actionDecrFontSize = config.createItem("decr-font-size") { main.decreaseFontSize() }
        val actionMoveEditorToLeft = config.createItem("editor-move-left") { main.editorToTheLeft() }
        val actionMoveEditorToRight = config.createItem("editor-move-right") { main.editorToTheRight() }

        file.items.setAll(
            actionNew,
            actionOpen,
            recentFiles,
            SeparatorMenuItem(),
            actionSave,
            actionSaveAs,
            SeparatorMenuItem(),
            actionClose,
        )
        view.items.setAll(
            actionIncrFontSize,
            actionDecrFontSize,
            SeparatorMenuItem(),
            actionMoveEditorToLeft,
            actionMoveEditorToRight
        )
        tools.items.setAll(actionRun)
    }

    private fun updateRecentFiles() {
        val rf = ctx.get<RecentFiles>().files
        recentFiles.items.setAll(
            rf.map { p ->
                val mi = MenuItem(p.fileName.toString())
                mi.onAction = EventHandler { main.open(p) }
                mi
            }
        )
    }
}

open class TitledPanel(header: String) {
    val ui = BorderPane()
    var buttonBox = HBox()
    val lblHeader = createHeaderLabel(header)

    //val btnMenu = Button()
    init {
        //btnMenu.graphic = FontIcon(AntDesignIconsFilled.ENVIRONMENT)
        //buttonBox.children.add(btnMenu)

        val spacer = Region()
        HBox.setHgrow(spacer, Priority.ALWAYS)

        ui.top = HBox(lblHeader, spacer, buttonBox)
        ui.styleClass.add("titled-panel")
    }

    protected fun createHeaderLabel(text: String) = Label(text).also {
        it.styleClass.add("title")
    }
}

class MultiTabPane(orientation: Orientation) : Controller {
    override val ui = BorderPane()
    val content = SplitPane()
    var buttonBar = ToolBar()
    private val buttons = FXCollections.observableArrayList<ToggleButton>()

    private var lastOpenedSize: Region = Region()

    //properties
    var orientationProperty = content.orientationProperty()
        .also {
            it.set(orientation)
            buttonBar.orientationProperty().bind(it)
            it.addListener { _, _, new -> reformat(new) }
        }
    var orientation by orientationProperty
    val tabs = SimpleListProperty<Tab>(this, "tabs", FXCollections.observableArrayList())
    //

    /*class MultiTabHandler(val splitPane: SplitPane) : ChangeListener<Node> {
        var dividerPosition = 0.0
        override fun changed(observable: ObservableValue<out Node>?, oldValue: Node?, newValue: Node?) {
            val idx = vSplit.dividers.lastIndex
            if (newValue == null) {
                dividerPosition = vSplit.dividerPositions.last()
                vSplit.setDividerPosition(idx, scene.height)
            } else {
                vSplit.setDividerPosition(idx, dividerPosition)
            }
        }
    }*/

    init {
        reformat(orientation)

        buttons.addListener(ListChangeListener { _ -> buttonBar.items.setAll(buttons.map { Group(it) }) })

        tabs.addListener(ListChangeListener { chg ->
            val states = buttons.map { it.isSelected }
            buttons.setAll(tabs.mapIndexed { idx, it ->
                createToggleButton(it, states.getOrNull(idx) ?: false)
            })
        })

        hideContentIfEmpty()
    }

    private fun reformat(orientation: Orientation) {
        if (orientation == Orientation.HORIZONTAL) {
            ui.center = content
            ui.left = Group()
            ui.bottom = buttonBar
            ui.styleClass.remove("vertical-multi-pane")
            ui.styleClass.add("horizontal-multi-pane")
        } else {
            ui.center = content
            ui.bottom = Group()
            ui.bottom.maxHeight(0.0)
            ui.left = buttonBar
            ui.styleClass.add("vertical-multi-pane")
            ui.styleClass.remove("horizontal-multi-pane")
        }
        hideContentIfEmpty()
    }

    private fun createToggleButton(tab: Tab, selected: Boolean = false) = ToggleButton().also {
        it.textProperty().bind(tab.textProperty())
        it.graphicProperty().bind(tab.graphicProperty())
        it.isSelected = selected
        it.selectedProperty().addListener { _, _, selected -> onSelectionChange(tab, selected) }
    }

    private fun onSelectionChange(tab: Tab, selected: Boolean?) {
        val selected = selected ?: false
        if (selected) {
            if (tab.content !in content.items)
                content.items.add(tab.content)
        } else {
            content.items.remove(tab.content)
        }
        hideContentIfEmpty()
    }

    private fun hideContentIfEmpty() {
        if (content.items.isEmpty()) {
            ui.center = Region()
            lastOpenedSize.prefWidth = content.width
            lastOpenedSize.prefHeight = content.height

            if (orientation == Orientation.VERTICAL)
                ui.maxWidth = buttonBar.width
            else
                ui.maxHeight = buttonBar.height
        } else {
            ui.center = content
            if (orientation == Orientation.VERTICAL)
                ui.maxWidth = -1.0
            else
                ui.maxHeight = -1.0

            ui.center.minWidth(lastOpenedSize.prefWidth)
            ui.center.minHeight(lastOpenedSize.prefHeight)
        }
    }

    /*inner class SelectionModel : MultipleSelectionModel<Tab>() {
        private val selectedTabs = SimpleListProperty<Tab>(this, "selectedTabs")
        private val indices = SimpleListProperty<Int>(this, "indices")

        init {
            indices.addListener(ListChangeListener {
                selectedTabs.setAll(
                    tabs.filterIndexed {idx,t-> idx in indices}.toMutableList())
            })
        }

        override fun clearAndSelect(index: Int) {
            indices.clear()
            indices.add(index)
        }

        override fun select(index: Int) {
            if (index !in indices)
                indices.add(index)
        }

        override fun select(obj: Tab?) {
            if (obj == null) return
            val idx = tabs.indexOf(obj)
            if (idx >= 0) select(idx)
        }

        override fun clearSelection(index: Int) {
            indices.remove(index)
        }

        override fun clearSelection() {
            indices.clear()
        }

        override fun isSelected(index: Int): Boolean = index in indices

        override fun isEmpty(): Boolean = indices.isEmpty()

        override fun selectPrevious() {}

        override fun selectNext() {}

        override fun selectFirst() {
            select(0)
        }

        override fun selectLast() {
            select(tabs.lastIndex)
        }

        override fun getSelectedIndices(): ObservableList<Int> {
            return indices
        }

        override fun getSelectedItems(): ObservableList<Tab> {
            return selectedTabs
        }

        override fun selectIndices(index: Int, vararg indices: Int) {
            select(index)
            indices.forEach { select(it) }
        }

        override fun selectAll() {
            tabs.forEachIndexed { idx, _ -> select(idx) }
        }
    }
*/
}


/*
class MultiTabPane(orientation: Orientation) : Controller {
    override val ui = BorderPane()
    val content = SplitPane()
    var buttonBar = ToolBar()
    private val buttons = FXCollections.observableArrayList<ToggleButton>()

    private var lastOpenedSize: Region = Region()

    //properties
    var orientationProperty = content.orientationProperty()
        .also {
            it.set(orientation)
            buttonBar.orientationProperty().bind(it)
            it.addListener { _, _, new -> reformat(new) }
        }
    var orientation by orientationProperty
    val tabs = SimpleListProperty<Tab>(this, "tabs", FXCollections.observableArrayList())
    //

    /*class MultiTabHandler(val splitPane: SplitPane) : ChangeListener<Node> {
        var dividerPosition = 0.0
        override fun changed(observable: ObservableValue<out Node>?, oldValue: Node?, newValue: Node?) {
            val idx = vSplit.dividers.lastIndex
            if (newValue == null) {
                dividerPosition = vSplit.dividerPositions.last()
                vSplit.setDividerPosition(idx, scene.height)
            } else {
                vSplit.setDividerPosition(idx, dividerPosition)
            }
        }
    }*/

    init {
        reformat(orientation)

        buttons.addListener(ListChangeListener { _ -> buttonBar.items.setAll(buttons.map { Group(it) }) })

        tabs.addListener(ListChangeListener { chg ->
            val states = buttons.map { it.isSelected }
            buttons.setAll(tabs.mapIndexed { idx, it ->
                createToggleButton(it, states.getOrNull(idx) ?: false)
            })
        })

        hideContentIfEmpty()
    }

    private fun reformat(orientation: Orientation) {
        if (orientation == Orientation.HORIZONTAL) {
            ui.center = content
            ui.left = Group()
            ui.bottom = buttonBar
            ui.styleClass.remove("vertical-multi-pane")
            ui.styleClass.add("horizontal-multi-pane")
        } else {
            ui.center = content
            ui.bottom = Group()
            ui.bottom.maxHeight(0.0)
            ui.left = buttonBar
            ui.styleClass.add("vertical-multi-pane")
            ui.styleClass.remove("horizontal-multi-pane")
        }
        hideContentIfEmpty()
    }

    private fun createToggleButton(tab: Tab, selected: Boolean = false) = ToggleButton().also {
        it.textProperty().bind(tab.textProperty())
        it.graphicProperty().bind(tab.graphicProperty())
        it.isSelected = selected
        it.selectedProperty().addListener { _, _, selected -> onSelectionChange(tab, selected) }
    }

    private fun onSelectionChange(tab: Tab, selected: Boolean?) {
        val selected = selected ?: false
        if (selected) {
            if (tab.content !in content.items)
                content.items.add(tab.content)
        } else {
            content.items.remove(tab.content)
        }
        hideContentIfEmpty()
    }

    private fun hideContentIfEmpty() {
        if (content.items.isEmpty()) {
            ui.center = Region()
            lastOpenedSize.prefWidth = content.width
            lastOpenedSize.prefHeight = content.height

            if (orientation == Orientation.VERTICAL)
                ui.maxWidth = buttonBar.width
            else
                ui.maxHeight = buttonBar.height
        } else {
            ui.center = content
            if (orientation == Orientation.VERTICAL)
                ui.maxWidth = -1.0
            else
                ui.maxHeight = -1.0

            ui.center.minWidth(lastOpenedSize.prefWidth)
            ui.center.minHeight(lastOpenedSize.prefHeight)
        }
    }

    /*inner class SelectionModel : MultipleSelectionModel<Tab>() {
        private val selectedTabs = SimpleListProperty<Tab>(this, "selectedTabs")
        private val indices = SimpleListProperty<Int>(this, "indices")

        init {
            indices.addListener(ListChangeListener {
                selectedTabs.setAll(
                    tabs.filterIndexed {idx,t-> idx in indices}.toMutableList())
            })
        }

        override fun clearAndSelect(index: Int) {
            indices.clear()
            indices.add(index)
        }

        override fun select(index: Int) {
            if (index !in indices)
                indices.add(index)
        }

        override fun select(obj: Tab?) {
            if (obj == null) return
            val idx = tabs.indexOf(obj)
            if (idx >= 0) select(idx)
        }

        override fun clearSelection(index: Int) {
            indices.remove(index)
        }

        override fun clearSelection() {
            indices.clear()
        }

        override fun isSelected(index: Int): Boolean = index in indices

        override fun isEmpty(): Boolean = indices.isEmpty()

        override fun selectPrevious() {}

        override fun selectNext() {}

        override fun selectFirst() {
            select(0)
        }

        override fun selectLast() {
            select(tabs.lastIndex)
        }

        override fun getSelectedIndices(): ObservableList<Int> {
            return indices
        }

        override fun getSelectedItems(): ObservableList<Tab> {
            return selectedTabs
        }

        override fun selectIndices(index: Int, vararg indices: Int) {
            select(index)
            indices.forEach { select(it) }
        }

        override fun selectAll() {
            tabs.forEachIndexed { idx, _ -> select(idx) }
        }
    }
*/
}
 */