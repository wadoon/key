package org.key_project.ide

import javafx.scene.control.Tab
import javafx.scene.control.TreeView

class FileOutline(ctx: Context) : TitledPanel("Outline") {
    val tab: Tab = Tab("Outline")
    val outlineTree = TreeView<OutlineEntry>()
    init {
        ctx.register(this)
        ui.center = outlineTree
        tab.content = ui
    }
}

class OutlineEntry(
    val title: String,
    val editor: Editor,
    val caretPosition: Int? = null
) {
    override fun toString(): String = title
}