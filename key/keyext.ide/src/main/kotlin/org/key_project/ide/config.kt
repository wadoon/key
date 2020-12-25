package org.key_project.ide

import de.uka.ilkd.key.settings.PathConfig
import javafx.collections.FXCollections
import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.scene.control.MenuItem
import javafx.scene.input.KeyCombination
import org.kordamp.ikonli.javafx.FontIcon
import org.kordamp.ikonli.javafx.IkonResolver
import java.io.File
import java.net.URL
import java.nio.file.Path
import java.nio.file.Paths
import java.util.*
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
    fun store() = save(ConfigurationPaths.appData)
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

    fun store() {
        println("Store recent fiels to ${ConfigurationPaths.recentFiles}")
        val lines = files.asSequence().map { it.toAbsolutePath().toString() }
        ConfigurationPaths.recentFiles.writeLines(lines)
    }
}


class UserConfig() : Configuration() {
    internal fun createItem(id: String, function: (ActionEvent) -> Unit): MenuItem {
        fun getActionValue(key: String): String? = properties["actions.$key"]?.toString() ?: null.also {
            System.err.println("actions.$key is not defined in config")
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

    fun store() = save(ConfigurationPaths.userConfig)
}