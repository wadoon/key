package org.key_project.ide

import javafx.application.Application
import javafx.scene.input.KeyCode
import javafx.scene.input.KeyCodeCombination
import javafx.stage.Modality
import javafx.stage.Stage
import org.fxmisc.wellbehaved.event.EventPattern.keyPressed
import org.fxmisc.wellbehaved.event.InputMap.*
import org.fxmisc.wellbehaved.event.Nodes
import org.fxmisc.wellbehaved.event.template.InputMapTemplate.*
import tornadofx.*
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
    val appData = ApplicationData().also { it.load() }
    val userConfig = UserConfig().also { it.load() }
    val recentFiles = RecentFiles().also { it.load() }
    val themeManager = ThemeManager(userConfig, appData)

    val context = Context()

    init {}

    override fun start(stage: Stage) {
        context.register(appData)
        context.register(userConfig)
        context.register(recentFiles)
        val main = MainScene(context)

        main.root.styleClass.addAll("root", userConfig.theme)

        themeManager.installCss(main.scene)
        stage.hookGlobalShortcuts()

        stage.x = appData.posX
        stage.y = appData.posY
        stage.width = appData.windowWidth
        stage.height = appData.windowHeight
        /*
        appData.posX.bind(primaryStage.xProperty())
        appData.posY.bind(primaryStage.yProperty())
        appData.windowWidth.bind(primaryStage.widthProperty())
        appData.windowHeight.bind(primaryStage.heightProperty())
        */
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
                consume(keyPressed(KeyCode.F12)) { e ->
                    //ScenicView.show(main.scene)
                    val ld =  find<LayoutDebugger>()
                    ld.debuggingScene = main.scene
                    ld.openModal(modality = Modality.NONE, owner = stage)
                },
            )
        )
        stage.show()
    }

    override fun stop() {
        appData.save()
        userConfig.save()
        recentFiles.save()
    }
}