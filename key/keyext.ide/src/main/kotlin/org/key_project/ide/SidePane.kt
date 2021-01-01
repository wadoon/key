package org.key_project.ide

import javafx.beans.property.SimpleListProperty
import javafx.beans.property.SimpleObjectProperty
import javafx.collections.FXCollections
import javafx.collections.ListChangeListener
import javafx.geometry.Orientation
import javafx.scene.Group
import javafx.scene.Node
import javafx.scene.control.SplitPane
import javafx.scene.control.Tab
import javafx.scene.control.ToggleButton
import javafx.scene.control.ToolBar
import javafx.scene.layout.BorderPane
import tornadofx.getValue
import tornadofx.setValue

/**
 *
 * @author Alexander Weigl
 * @version 1 (1/1/21)
 */
class SidePane(position: Position) : Controller {
    enum class Position {
        LEFT {
            override fun reformat(pane: SidePane) {
                with(pane) {
                    toolButtons.orientation = Orientation.VERTICAL
                    center.orientation = Orientation.HORIZONTAL
                    toolPanels.orientation = Orientation.VERTICAL
                    center.items.setAll(toolPanels, content)

                    //ui.center = toolPanels
                    ui.bottom = Group()
                    ui.bottom.maxHeight(0.0)
                    ui.left = toolButtons
                    ui.center = center
                    SplitPane.setResizableWithParent(toolPanels, false)
                }
            }
        },
        DOWN {
            override fun reformat(pane: SidePane) {
                with(pane) {
                    toolButtons.orientation = Orientation.HORIZONTAL
                    center.orientation = Orientation.VERTICAL
                    toolPanels.orientation = Orientation.HORIZONTAL

                    center.items.setAll(content, toolPanels)

                    ui.center = center
                    ui.left = null
                    ui.bottom = toolButtons
                    SplitPane.setResizableWithParent(toolPanels, false)
                }
            }
        },
        /**
         * Untested
         */
        RIGHT {
            override fun reformat(pane: SidePane) {
                with(pane) {
                    LEFT.reformat(this)
                    center.items.setAll(content, toolPanels)
                }
            }
        },
        UP {
            override fun reformat(pane: SidePane) {
                with(pane) {
                    DOWN.reformat(this)
                    center.items.setAll(toolPanels, content)
                }
            }
        };


        abstract fun reformat(pane: SidePane)
    }

    override val ui = BorderPane()
    private val toolPanels = SplitPane()
    private val toolButtons = ToolBar()
    private val center = SplitPane()


    private val buttons = FXCollections.observableArrayList<ToggleButton>()
    private var lastDividerPosition = -1.0

    //properties
    val contentProperty = SimpleObjectProperty<Node>().also {
        it.addListener { _ -> position.reformat(this) }
    }
    var content: Node by contentProperty

    val positionProperty = SimpleObjectProperty<Position>(this, "position", position).also {
        it.addListener { _, _, new -> new.reformat(this) }
    }
    var position by positionProperty

    val tabs = SimpleListProperty<Tab>(this, "tabs", FXCollections.observableArrayList())
    //

    init {
        ui.styleClass.add("side-pane")

        buttons.addListener(ListChangeListener { _ -> toolButtons.items.setAll(buttons.map { Group(it) }) })

        tabs.addListener(ListChangeListener { chg ->
            val states = buttons.map { it.isSelected }
            buttons.setAll(tabs.mapIndexed { idx, it ->
                createToggleButton(it, states.getOrNull(idx) ?: false)
            })
        })

        position.reformat(this)
        onContentVisibilityChange()
    }

    private fun createToggleButton(tab: Tab, selected: Boolean = false) = ToggleButton().also {
        it.textProperty().bind(tab.textProperty())
        it.graphicProperty().bind(tab.graphicProperty())
        it.isSelected = selected
        it.selectedProperty().addListener { _, _, selected -> onSelectionChange(tab, selected) }
    }

    private fun onSelectionChange(tab: Tab, selected: Boolean?) {
        if (selected ?: false) {
            if (tab.content !in toolPanels.items)
                toolPanels.items.add(tab.content)
        } else {
            toolPanels.items.remove(tab.content)
        }
        onContentVisibilityChange()
    }

    private fun onContentVisibilityChange() {
        if (toolPanels.items.isEmpty()) { // if tool panels are empty
            lastDividerPosition = center.dividerPositions.first()
            val max = when(position) {
                Position.LEFT,Position.RIGHT -> 0.0
                else -> content?.layoutBounds?.height ?: 100.0
            }
            center.setDividerPosition(0, max)
        } else {
            if (lastDividerPosition < 0.0) {
                lastDividerPosition = 0.2 * when(position) {
                    Position.LEFT,Position.RIGHT -> ui.width
                    else -> ui.height
                }
            }
            center.setDividerPosition(0, lastDividerPosition)
        }
    }
}