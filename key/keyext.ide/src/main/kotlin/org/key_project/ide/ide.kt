package org.key_project.ide

import javafx.application.Application
import javafx.beans.property.SimpleListProperty
import javafx.beans.property.SimpleObjectProperty
import javafx.beans.value.ObservableValue
import javafx.collections.FXCollections
import javafx.collections.ListChangeListener
import javafx.collections.ObservableList
import javafx.event.ActionEvent
import javafx.event.Event
import javafx.event.EventHandler
import javafx.geometry.Orientation
import javafx.scene.Node
import javafx.scene.Scene
import javafx.scene.control.*
import javafx.scene.control.cell.TextFieldTreeCell
import javafx.scene.layout.*
import javafx.stage.FileChooser
import javafx.stage.Stage
import javafx.util.StringConverter
import org.kordamp.ikonli.fontawesome5.FontAwesomeRegular
import org.kordamp.ikonli.javafx.FontIcon
import tornadofx.getValue
import tornadofx.readonlyColumn
import tornadofx.setValue
import java.awt.Desktop
import java.io.IOException
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import kotlin.io.path.ExperimentalPathApi
import kotlin.io.path.exists
import kotlin.io.path.readText
import kotlin.io.path.writeText


@ExperimentalPathApi
class IdeApp : Application() {
    val appData = ApplicationData().also { it.load() }
    val userConfig = UserConfig().also { it.load() }
    val recentFiles = RecentFiles().also { it.load() }
    val themeManager = ThemeManager(userConfig, appData)

    val context = Context()

    override fun start(primaryStage: Stage) {
        context.register(appData)
        context.register(userConfig)
        context.register(recentFiles)
        val main = MainScene(context)

        main.root.styleClass.addAll("root", "dark")
        themeManager.installCss(main.scene)

        primaryStage.scene = main.scene

        primaryStage.x = appData.posX
        primaryStage.y = appData.posY
        primaryStage.width = appData.windowWidth
        primaryStage.height = appData.windowHeight
        /*
        appData.posX.bind(primaryStage.xProperty())
        appData.posY.bind(primaryStage.yProperty())
        appData.windowWidth.bind(primaryStage.widthProperty())
        appData.windowHeight.bind(primaryStage.heightProperty())
        */
        primaryStage.title = ConfigurationPaths.applicationName

        val projectDir = parameters.named["p"]
        projectDir?.let {
            val p = Paths.get(it)
            if (p.exists())
                main.fileNavigator.rootFile = p
        }

        for (file in parameters.unnamed) {
            if (file == "%") {
                main.addEditorTabPane()
                continue
            }
            val p = Paths.get(file)
            if (p.exists()) main.open(p)
        }


        primaryStage.show()
    }

    override fun stop() {
        appData.save()
        userConfig.save()
        recentFiles.save()
    }
}

interface Controller {
    val ui: Node
}

interface TabbedPane {
    val tab: Tab
}


@OptIn(ExperimentalPathApi::class)
class MainScene(val context: Context) {
    //region controllers
    val menu = IdeMenu(context)
    val fileNavigator = FileNavigator(context)
    val outline = FileOutline(context)
    //endregion

    val root = BorderPane()
    val scene = Scene(root, 300.0, 300.0)
    val paneNavigation = SplitPane()
    val hSplit = SplitPane()
    val vSplit = SplitPane()
    val paneTool = MultiTabPane()
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
        paneNavigation.items.setAll(outline.ui, fileNavigator.ui)
        hSplit.items.add(paneNavigation)
        hSplit.items.addAll(editorTabPanes)

        paneNavigation.maxWidthProperty().bind(hSplit.widthProperty().multiply(0.25));

        val appData = context.get<ApplicationData>()
        fileNavigator.rootFile = Paths.get(appData.lastNavigatorPath)

        hSplit.items.add(createEditorTabPane())

        //paneTool.tabClosingPolicy = TabPane.TabClosingPolicy.ALL_TABS
        /*paneTool.tabs.addListener(ChangeListener({ _, _, _ ->
            vSplit.setDividerPosition(0,1)
        })*/

        paneTool.ui.centerProperty().addListener(object : javafx.beans.value.ChangeListener<Node> {
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
        })
        addToolPanel(problems)

        SplitPane.setResizableWithParent(paneTool.ui, false)
        SplitPane.setResizableWithParent(paneNavigation, false)
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


    fun close() {
        closeEditorTab()
    }

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

}

class MultiTabPane : Controller {
    override val ui = BorderPane()
    val content = SplitPane()
    val buttonBar = HBox()
    val tabs = SimpleListProperty<Tab>(this, "tabs", FXCollections.observableArrayList())
    private val buttons = FXCollections.observableArrayList<ToggleButton>()

    init {
        ui.center = content
        ui.bottom = buttonBar

        buttons.addListener(ListChangeListener { _ -> buttonBar.children.setAll(buttons) })

        tabs.addListener(ListChangeListener { chg ->
            val states = buttons.map { it.isSelected }
            buttons.setAll(tabs.mapIndexed { idx, it ->
                createToggleButton(it, states.getOrNull(idx) ?: false)
            })
        })

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
            ui.center = null //hide content
        } else {
            ui.center = content
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

class IssueList(context: Context) : Controller, TabbedPane, TitledPanel("Issues") {
    //val view = TreeTableView<IssueEntry>()
    val view = TableView<IssueEntry>()
    override val tab: Tab = Tab().also { it.content = ui }

    init {
        context.register(this)

        tab.text = "Issues"
        tab.graphic = FontIcon(FontAwesomeRegular.BELL)
        ui.center = view
        lblHeader.graphic = FontIcon(FontAwesomeRegular.BELL)

        view.readonlyColumn("Title", IssueEntry::title)
        view.readonlyColumn("Category", IssueEntry::category)
        view.readonlyColumn("Offset", IssueEntry::offset)
    }
}

data class IssueEntry(val title: String, val category: String, val offset: Int) {
    //val children = mutableListOf<IssueEntry>()
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
        context.register(this)
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
        val actionIncrFontSize = config.createItem("incr-font-size") {}
        val actionDecrFontSize = config.createItem("decr-font-size") {}
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

abstract class TitledPanel(header: String) {
    val ui = BorderPane()
    val buttonBox = HBox()
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

class FileNavigator(ctx: Context) : TitledPanel("Navigator") {
    private val config = ctx.get<UserConfig>()
    private val main by ctx.ref<MainScene>()

    //properties
    val rootFileProperty = SimpleObjectProperty(this, "rootFile", Paths.get(".").normalize().toAbsolutePath())
    var rootFile by rootFileProperty
    //end properties

    //ui
    val treeFile = TreeView(SimpleFileTreeItem(rootFile))
    val contextMenu: ContextMenu = ContextMenu()
    //end

    private fun markFolderUnderMouse(event: ActionEvent) {}

    private val actionOpenFile = config.createItem("tree-open-file") {
        markFolderUnderMouse(it)
        treeFile.selectionModel.selectedItem?.let {
            main.open(it.value)
        }
    }
    private val actionNewFile = config.createItem("tree-new-file") {
        markFolderUnderMouse(it)
        treeFile.selectionModel.selectedItem?.let { item ->
            val path = item.value!!
            val dialog = TextInputDialog()
            dialog.contentText = "File name:"
            val name = dialog.showAndWait()
            name.ifPresent {
                val newFile = path.resolve(it)
                try {
                    Files.createFile(newFile)
                    main.open(newFile)
                    refresh()
                } catch (e: IOException) {
                    val a = Alert(Alert.AlertType.ERROR)
                    a.contentText = e.message
                    a.show()
                }
            }
        }
    }
    private val actionNewDirectory = config.createItem("tree-new-directory") {
        markFolderUnderMouse(it)
        treeFile.selectionModel.selectedItem?.let { item ->
            val path = item.value!!
            val dialog = TextInputDialog()
            dialog.contentText = "Folder name:"
            val name = dialog.showAndWait()
            name.ifPresent {
                val newFile = path.resolve(it)
                try {
                    Files.createDirectory(newFile)
                    main.open(newFile)
                    refresh()
                } catch (e: IOException) {
                    val a = Alert(Alert.AlertType.ERROR)
                    a.contentText = e.message
                    a.show()
                }
            }
        }
    }
    private val actionRenameFile = config.createItem("tree-rename-file") { }
    private val actionDeleteFile = config.createItem("tree-delete-file") {}
    private val actionGoUp = config.createItem("go-up") {
        markFolderUnderMouse(it)
        treeFile.root.value?.let { file ->
            treeFile.root = SimpleFileTreeItem(file.parent.toAbsolutePath())
            treeFile.root.isExpanded = true
        }
    }
    private val actionGoInto = config.createItem("go-into") {
        markFolderUnderMouse(it)
        (treeFile.selectionModel.selectedItem)?.let { file ->
            treeFile.root = SimpleFileTreeItem(file.value.toAbsolutePath())
            treeFile.root.isExpanded = true
        }
    }
    private val actionRefresh = config.createItem("refresh") { refresh() }

    private fun refresh() {}

    private val actionExpandSubTree = config.createItem("expand-tree") {
        markFolderUnderMouse(it)
    }
    private val actionOpenExplorer = config.createItem("open-in-explorer") {
        markFolderUnderMouse(it)
        (treeFile.selectionModel.selectedItem)?.let { file ->
            try {
                Desktop.getDesktop()?.browseFileDirectory(file.value.toFile())
            } catch (e: UnsupportedOperationException) {
                ProcessBuilder("explorer", "/select,${file.value}").start()
            }
        }
    }

    private val actionOpenSystem = config.createItem("xdg-open") {
        markFolderUnderMouse(it)
        (treeFile.selectionModel.selectedItem)?.let { file ->
            try {
                Desktop.getDesktop()?.open(file.value.toFile())
            } catch (e: UnsupportedOperationException) {
                ProcessBuilder("explorer", "/select,${file.value}").start()
            }
        }
    }

    init {
        contextMenu.items.setAll(
            actionOpenFile,
            SeparatorMenuItem(),
            actionNewFile,
            actionNewDirectory,
            actionRenameFile,
            actionDeleteFile,
            SeparatorMenuItem(),
            actionGoUp,
            actionGoInto,
            SeparatorMenuItem(),
            actionExpandSubTree,
            actionRefresh,
            SeparatorMenuItem(),
            actionOpenExplorer,
            actionOpenSystem
        )


        treeFile.contextMenu = contextMenu
        treeFile.isEditable = false
        treeFile.isShowRoot = true
        rootFileProperty.addListener { _, _, new ->
            treeFile.root = SimpleFileTreeItem(new)
        }
        ui.center = treeFile
        treeFile.setCellFactory { tv ->
            TextFieldTreeCell(object : StringConverter<Path>() {
                override fun toString(obj: Path?): String = obj?.fileName.toString() ?: ""
                override fun fromString(string: String?): Path = Paths.get(string)
            })
        }
        treeFile.root.isExpanded = true
    }
}

class SimpleFileTreeItem(f: Path) : TreeItem<Path>(f) {
    private var isFirstTimeChildren = true
    private var isFirstTimeLeaf = true
    private var isLeaf = false

    override fun getChildren(): ObservableList<TreeItem<Path>> {
        if (isFirstTimeChildren) {
            isFirstTimeChildren = false
            super.getChildren().setAll(buildChildren(this))
        }
        return super.getChildren()
    }

    override fun isLeaf(): Boolean {
        if (isFirstTimeLeaf) {
            isFirstTimeLeaf = false
            val f = value as Path
            isLeaf = Files.isRegularFile(f)
        }
        return isLeaf
    }

    private fun buildChildren(node: TreeItem<Path>): ObservableList<TreeItem<Path>> {
        val f = node.value
        if (f != null && Files.isDirectory(f)) {
            val children: ObservableList<TreeItem<Path>> = FXCollections.observableArrayList()
            Files.list(f).sorted().forEach {
                children.add(SimpleFileTreeItem(it))
            }
            return children
        }
        return FXCollections.emptyObservableList()
    }
}

class FileOutline(ctx: Context) : TitledPanel("Outline") {
    val outlineTree = TreeView<OutlineEntry>()

    init {
        ctx.register(this)
        ui.center = outlineTree
    }
}

class OutlineEntry(
    val title: String,
    val editor: Editor,
    val caretPosition: Int? = null
) {
    override fun toString(): String = title
}