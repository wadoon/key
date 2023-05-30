import javafx.geometry.Side
import javafx.scene.Parent
import javafx.scene.control.TextArea
import net.miginfocom.layout.AC
import net.miginfocom.layout.LC
import org.tbee.javafx.scene.layout.MigPane
import tornadofx.*

/**
 *
 * @author Alexander Weigl
 * @version 1 (30.05.23)
 */

class StategySettingsView : View("Strategy Settings") {
    override val root: Parent = MigPane(LC().fillY(), AC().fill()).also {
        it.add(label("Test"))
        it.add(textfield())

        it.add(label("Test"))
        it.add(textfield())

        it.add(label("Test"))
        it.add(textfield())

        it.add(label("Test"))
        it.add(textfield())
    }

}

class MainView : View("KeY") {
    private val settingsDialog = StategySettingsView()

    val leftToolsPane =
            drawer(multiselect = true, floatingContent = true, side = Side.LEFT) {
                item(settingsDialog.titleProperty) {
                    add(settingsDialog.root)
                }

                item("test") {
                    flowpane {
                        label("Test")
                        label("Test")
                        label("Test")
                        label("Test")
                        label("Test")
                        label("Test")
                        label("Test")
                    }
                }
            }

    val rightToolsPane =
            drawer(multiselect = true, floatingContent = true, side = Side.RIGHT) {

            }

    val bottomToolsPane =
            drawer(multiselect = true, floatingContent = true, side = Side.BOTTOM) {

            }

    val rootMenuBar =
            menubar {
                menu("File") {
                    item("Load")
                    item("Load Examples")
                    item("Save")
                }

                menu("View") {

                }

                menu("Proof") {

                }

                menu("About") {

                }
            }

    val centerPanels =
            tabpane {
            }

    override val root: Parent
        get() = myRoot

    val myRoot = borderpane {
        top = rootMenuBar
        left = leftToolsPane
        right = rightToolsPane
        bottom = bottomToolsPane
        center = centerPanels
    }
}

class KeyApplication : App(MainView::class) {

}

fun main(args: Array<String>) {
    launch<KeyApplication>(args)
}