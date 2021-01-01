package org.key_project.ide

import javafx.application.Application
import javafx.scene.input.KeyCode
import javafx.stage.Modality
import javafx.stage.Stage
import org.fxmisc.wellbehaved.event.EventPattern.keyPressed
import org.fxmisc.wellbehaved.event.InputMap.consume
import org.fxmisc.wellbehaved.event.InputMap.sequence
import org.fxmisc.wellbehaved.event.Nodes
import tornadofx.App
import tornadofx.LayoutDebugger
import tornadofx.find
import tornadofx.hookGlobalShortcuts
import java.nio.file.Paths
import kotlin.io.path.ExperimentalPathApi
import kotlin.io.path.exists


object KeyIde {
    @ExperimentalPathApi
    @JvmStatic
    fun main(args: Array<String>) {
        Application.launch(IdeApp::class.java, *args)
    }
}

@ExperimentalPathApi
class IdeApp : App(MainScene::class) {
    private val appData = ApplicationData().also { it.load() }
    private val userConfig = UserConfig().also { it.load() }
    private val recentFiles = RecentFiles().also { it.load() }
    private val themeManager = ThemeManager(userConfig, appData)
    private lateinit var stage: Stage
    private val context = Context()


    override fun start(stage: Stage) {
        this.stage = stage

        context.register(appData)
        context.register(userConfig)
        context.register(recentFiles)
        context.register(themeManager)
        val main = MainScene(context)

        main.root.styleClass.addAll("root", userConfig.theme)

        themeManager.installCss(main.scene)
        stage.hookGlobalShortcuts()

        stage.x = appData.posX
        stage.y = appData.posY
        stage.width = appData.windowWidth
        stage.height = appData.windowHeight
        stage.title = ConfigurationPaths.applicationName

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
        stage.scene = main.scene

        Nodes.addInputMap(
            main.root, sequence(
                consume(keyPressed(KeyCode.F12)) {
                    val ld = find<LayoutDebugger>()
                    ld.debuggingScene = main.scene
                    ld.openModal(modality = Modality.NONE, owner = stage)
                },
            )
        )
        stage.show()
    }

    override fun stop() {
        appData.posX = stage.x
        appData.posY = stage.y
        appData.windowWidth = stage.width
        appData.windowHeight = stage.height

        appData.save()
        userConfig.save()
        recentFiles.save()
    }
}