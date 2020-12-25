package org.key_project.ide

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import javafx.application.Application
import javafx.beans.property.SimpleObjectProperty
import javafx.collections.FXCollections
import javafx.collections.ListChangeListener
import javafx.collections.ObservableList
import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.geometry.Orientation
import javafx.scene.Node
import javafx.scene.Scene
import javafx.scene.control.*
import javafx.scene.control.cell.TextFieldTreeCell
import javafx.scene.layout.BorderPane
import javafx.scene.layout.HBox
import javafx.scene.layout.VBox
import javafx.scene.text.Font
import javafx.stage.FileChooser
import javafx.stage.Stage
import javafx.util.StringConverter
import java.awt.Desktop
import java.io.IOException
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import kotlin.io.path.ExperimentalPathApi
import kotlin.io.path.readText
import kotlin.io.path.writeText
import kotlin.reflect.KProperty

class Context {
    private val map = HashMap<Class<*>, Any>()
    inline fun <reified T : Any> register(obj: T) = register(obj, T::class.java)
    fun <T : Any> register(obj: T, clazz: Class<T>) = obj.also { map[clazz] = it }
    inline fun <reified T : Any> get(): T = get(T::class.java)
    fun <T : Any> get(clazz: Class<T>): T = map[clazz] as T

    interface ReadOnlyProp<T> {
        operator fun getValue(self: Any, property: KProperty<*>): T
    }

    inline fun <reified T : Any> ref() = object : ReadOnlyProp<T> {
        override operator fun getValue(self: Any, property: KProperty<*>): T {
            return get(T::class.java)
        }
    }
}


class Arguments : CliktCommand() {
    val projectDir by option("-p").file()
    val files by argument().file().multiple()

    @ExperimentalPathApi
    override fun run() {
    }
}

@ExperimentalPathApi
class IdeApp : Application() {
    val appData = ApplicationData().also { it.load() }
    val userConfig = UserConfig().also { it.load() }
    val recentFiles = RecentFiles().also { it.load() }

    val context = Context()

    override fun start(primaryStage: Stage) {
        val args = Arguments()
        args.main(getParameters().raw)
        context.register(args)
        context.register(appData)
        context.register(userConfig)
        context.register(recentFiles)
        val main = MainScene(context)
        main.scene.stylesheets.addAll(
            javaClass.getResource("/css/style.css").toExternalForm()
        )
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
        primaryStage.show()
    }

    override fun stop() {
        appData.store()
        userConfig.store()
        recentFiles.store()
    }
}

interface Controller {
    val ui: Node
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
    val left = SplitPane()
    val center = SplitPane()
    val editorTabPanes = arrayListOf(createEditorTabPane())
    val statusBar = Label("")
    val openEditors = arrayListOf<Editor>()

    init {
        context.register<MainScene>(this)
        root.top = menu.ui
        root.center = center
        left.items.setAll(outline.ui, fileNavigator.ui)
        left.orientation = Orientation.VERTICAL
        center.items.add(left)
        center.items.addAll(editorTabPanes)

        val appData = context.get<ApplicationData>()
        fileNavigator.rootFile.value = Paths.get(appData.lastNavigatorPath)

        val args = context.get<Arguments>()
        args.projectDir?.let {
            fileNavigator.rootFile.value = it.toPath()
        }

        for (file in args.files) {
            open(file.toPath())
        }
    }

    fun publishMessage(status: String, graphic: Node? = null) {
        statusBar.text = status
        statusBar.graphic = graphic
    }

    private fun createEditorTabPane(): TabPane {
        return TabPane()
    }

    fun createCodeEditor() {
        addEditorTab(Editor(context))
    }

    fun addEditorTab(editor: Editor) {
        val tabPanel = editorTabPanes.first()
        val tab = Tab(editor.title.value, editor.ui)
        tabPanel.tabs.add(tab)
        editor.title.addListener { _, _, new -> tab.text = new }
        openEditors.add(editor)
        editor.ui.focusedProperty().addListener { obs, _, new -> if (new) currentEditor.value = editor }
        currentEditor.value = editor
        editor.ui.requestFocus()
    }

    val currentEditor = SimpleObjectProperty<Editor>(this, "currentEditor", null)

    fun close() {}

    fun saveAs(editor: Editor? = currentEditor.value) =
        editor?.also {
            val fileChooser = FileChooser()
            fileChooser.showSaveDialog(scene.window)?.let { new ->
                editor.filename.value = new.toPath()
                save(editor)
            }
        }

    fun save(editor: Editor? = currentEditor.value) {
        editor?.also { editor ->
            editor.filename.value?.also { filename ->
                filename.writeText(editor.ui.text)
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
        editor.filename.value = f
        editor.ui.insertText(0, f.readText())
        addEditorTab(editor)
    }

    fun editorToTheRight(editor: Editor? = currentEditor.value) {
        if (editor == null) return
        val tabPane = editorTabPanes.find { it.tabs.any { tab -> tab.content == editor.ui } }
        if (tabPane != null) {
            val tabIndex = editorTabPanes.indexOf(tabPane)
            if (tabPane == editorTabPanes.last()) {
                createEditorTabPane().also { editorTabPanes.add(it); center.items.add(it) }
            }
            val target = editorTabPanes[tabIndex + 1]
            val tab = tabPane.tabs.find { it.content == editor.ui }!!
            tabPane.tabs.remove(tab)
            target.tabs.add(tab)
        }
    }

    fun editorToTheLeft(editor: Editor? = currentEditor.value) {
        val tabPane = editorTabPanes.find { it.tabs.any { it.content == editor } }
        if (tabPane != null) {
            val tabIndex = editorTabPanes.indexOf(tabPane)
            if (tabPane == editorTabPanes.first()) {
                createEditorTabPane().also { editorTabPanes.add(0, it) }
            }
            val target = editorTabPanes[tabIndex - 1]
            val tab = tabPane.tabs.find { it.content == editor }!!
            tabPane.tabs.remove(tab)
            target.tabs.add(tab)
        }
    }
}

internal fun createHeaderLabel(text: String) = Label(text).also {
    it.font = Font(it.font.name, it.font.size + 6)
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
    val ui
        get() = root
    val root = BorderPane()
    val buttonBox = HBox()

    init {
        root.top = VBox(createHeaderLabel(header), buttonBox, Separator())
    }
}

class FileNavigator(ctx: Context) : TitledPanel("Navigator") {
    private val config = ctx.get<UserConfig>()
    private val main by ctx.ref<MainScene>()

    //properties
    val rootFile = SimpleObjectProperty(this, "rootFile", Paths.get(".").normalize().toAbsolutePath())
    //end properties

    //ui
    val treeFile = TreeView(SimpleFileTreeItem(rootFile.value))
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
        (treeFile.root.value as? Path)?.let { file ->
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
        rootFile.addListener { _, _, new ->
            treeFile.root = SimpleFileTreeItem(new)
        }
        root.center = treeFile
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
        root.center = outlineTree
    }
}

class OutlineEntry(
    val title: String,
    val editor: Editor,
    val caretPosition: Int? = null
) {
    override fun toString(): String = title
}