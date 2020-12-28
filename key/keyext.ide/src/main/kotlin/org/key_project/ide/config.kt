package org.key_project.ide

import de.uka.ilkd.key.settings.PathConfig
import de.uka.ilkd.key.util.KeYConstants
import javafx.application.Platform
import javafx.collections.FXCollections
import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.scene.Scene
import javafx.scene.control.MenuItem
import javafx.scene.input.KeyCombination
import org.kordamp.ikonli.javafx.FontIcon
import org.kordamp.ikonli.javafx.IkonResolver
import java.io.File
import java.net.URL
import java.nio.file.*
import java.nio.file.StandardWatchEventKinds.*
import java.util.*
import kotlin.collections.HashMap
import kotlin.io.path.*
import kotlin.reflect.KProperty


/**
 *
 * @author Alexander Weigl
 * @version 1 (12/24/20)
 */

object ConfigurationPaths {
    val operationSystem by lazy {
        val os = System.getProperty("os.name")
        when {
            os.contains("Mac") -> "mac"
            os.contains("Windows") -> "win"
            os.contains("Linux") -> "lin"
            else -> ""
        }
    }
    val applicationName = "key-ide"
    val configFolder = Paths.get(PathConfig.getKeyConfigDir())
    val userConfig = configFolder.resolve("key-ide-config.properties")
    val appData = configFolder.resolve("key-ide-data.properties")
    val recentFiles = configFolder.resolve("key-ide-recentfiles")

    init {
        logger.info { "Linked against: ${KeYConstants.VERSION}" }
        logger.info { "Linked against: ${KeYConstants.COPYRIGHT}" }
    }
}


class PropertiesProperty<T>(
    val default: T,
    val read: (String) -> T?,
    val write: (T) -> String = { it.toString() }
) {
    operator fun getValue(config: Configuration, prop: KProperty<*>): T =
        config.properties.getProperty(config.prefix + prop.name)?.let(read) ?: default

    operator fun setValue(config: Configuration, prop: KProperty<*>, v: T) {
        config.properties.setProperty(config.prefix + prop.name, write(v))
    }
}

@OptIn(ExperimentalPathApi::class)
abstract class Configuration(
    val properties: Properties = Properties(),
    val prefix: String = ""
) {

    protected fun integer(default: Int = 0) = PropertiesProperty(default, { it.toIntOrNull() })
    protected fun double(default: Double = .0) = PropertiesProperty(default, { it.toDoubleOrNull() })
    protected fun string(default: String = "") = PropertiesProperty(default, { it })
    protected fun boolean(default: Boolean) = PropertiesProperty(default, { it.equals("true", true) })

    fun load(path: Path) {
        if (path.exists())
            properties.load(path.bufferedReader())
    }

    fun load(resource: URL?) {
        resource?.openStream()?.use {
            properties.load(it)
        }
    }

    fun save(configuration: Path) {
        configuration.bufferedWriter().use {
            properties.store(it, "automatically saved, do not change.")
        }
    }
}

class ApplicationData : Configuration() {
    var posX by double(10.0)
    var posY by double(10.0)
    var windowHeight by double(400.0)
    var windowWidth by double(600.0)
    var lastNavigatorPath by string(File(".").absolutePath)

    fun load() = load(ConfigurationPaths.appData)
    fun save() = save(ConfigurationPaths.appData)
}


@OptIn(ExperimentalPathApi::class)
class RecentFiles {
    val files = FXCollections.observableArrayList<Path>()
    fun load() = load(ConfigurationPaths.recentFiles)
    fun load(p: Path) {
        if (p.exists()) {
            p.readLines().map { Paths.get(it) }
                .forEach { files.add(it) }
        }
    }

    fun save() {
        logger.info {"Store recent-files to ${ConfigurationPaths.recentFiles}"}
        val lines = files.map { it.toAbsolutePath().toString() }
        ConfigurationPaths.recentFiles.writeLines(lines)
    }
}


class UserConfig() : Configuration() {
    val theme by string("light")

    internal fun createItem(id: String, function: (ActionEvent) -> Unit): MenuItem {
        fun getActionValue(key: String): String? = properties["actions.$key"]?.toString() ?: null.also {
            logger.warn { "actions.$key is not defined in config" }
        }

        val resolver = IkonResolver.getInstance()
        val name = getActionValue("$id.name") ?: id
        val icon = getActionValue("$id.icon")?.let { ref ->
            resolver.resolve(ref).resolve(ref)?.let { FontIcon(it) }
        }
        val accel = getActionValue("$id.accel")?.let { KeyCombination.keyCombination(it) }
        val mi = MenuItem(name, icon)
        mi.onAction = EventHandler(function)
        mi.accelerator = accel
        return mi
    }

    fun load() {
        load(javaClass.getResource("/user-config.default.properties"))
        load(ConfigurationPaths.userConfig)
    }

    fun save() {
        logger.info {"Store user config to ${ConfigurationPaths.userConfig}"}
        save(ConfigurationPaths.userConfig)
    }
}

interface FileUpdateListener {
    /**
     * The file has been updated. A new call will not result until the file has been modified again.
     */
    fun fileUpdated(p: Path)
}

object FileUpdateMonitor : Runnable {
    var  isActive: Boolean = true
    var watchService = FileSystems.getDefault().newWatchService()

    private val monitor = Thread(null, this, "file-watcher").also { it.isDaemon=true; it.start() }

    private val watchKeys = HashMap<Path, WatchKey>()
    private val listeners = HashMap<WatchKey, (Path) -> Unit>()
    private val paths = HashMap<WatchKey, Path>()

    fun addListener(file: Path, listener: (Path) -> Unit) {
        if(Files.isRegularFile(file)) {
            addListener(file.parent, listener)
            return
        }

        val watchKey = file.register(watchService, ENTRY_CREATE, ENTRY_DELETE, ENTRY_MODIFY)
        watchKeys[file] = watchKey
        listeners[watchKey] = listener
        paths[watchKey] = file
    }

    fun removeListener(listener: (Path) -> Unit) {

    }

    fun removeListener(path: Path) {

    }

    /**
     * stops watching for changes
     */
    fun shutdown() {
        monitor.interrupt()
    }

    override fun run() {
        while (!monitor.isInterrupted) {
            var key: WatchKey? = null
            do {
                key = watchService.take()
                if (key != null) {
                    if (key.pollEvents().isNotEmpty() && isActive) {
                        synchronized(listeners) {
                            listeners[key]?.invoke(paths[key]!!)
                        }
                    }
                    key.reset()
                }
            } while (key != null)
        }
    }
}


class ThemeManager(
    val userConfig: UserConfig,
    val applicationData: ApplicationData
) {
    val baseCss = javaClass.getResource("/css/Base.css")
    val lightCss = javaClass.getResource("/css/Light.css")
    val darkCss = javaClass.getResource("/css/Dark.css")
    val themeCss = if (userConfig.theme == "dark") darkCss else lightCss

    fun installCss(scene: Scene) {
        addAndWatchForChanges(scene, baseCss, FileUpdateMonitor, 0)
        addAndWatchForChanges(scene, themeCss, FileUpdateMonitor, 1)
        /*if (appearancePreferences.shouldOverrideDefaultFontSize()) {
            scene.root.style = "-fx-font-size: " + appearancePreferences.getMainFontSize().toString() + "pt;"
        }*/
    }

    private fun addAndWatchForChanges(scene: Scene, cssFile: URL, fileUpdateMonitor: FileUpdateMonitor, index: Int) {
        scene.stylesheets.add(index, cssFile.toExternalForm())
        try {
            val cssUri = cssFile.toURI()
            if (!cssUri.toString().contains("jrt")) {
                logger.debug { "CSS URI: $cssUri"}
                val cssPath: Path = Path.of(cssUri).toAbsolutePath()
                logger.debug {"Enabling live reloading of $cssPath"}
                fileUpdateMonitor.addListener(cssPath) { _ ->
                    logger.debug { "Reload css file $cssFile"}
                    Platform.runLater {
                        scene.stylesheets.remove(cssFile.toExternalForm())
                        scene.stylesheets.add(index, cssFile.toExternalForm())
                    }
                }
            }
        } catch (e: Exception) {
            e.printStackTrace()
        }
    }
}