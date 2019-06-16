package org.key_project.ui.interactionlog.api

/**
 * @author Alexander Weigl
 * @version 1 (08.05.19)
 */
interface Scriptable {
    val proofScriptRepresentation: String
        get() = "// Unsupported interaction: $javaClass\n"
}
