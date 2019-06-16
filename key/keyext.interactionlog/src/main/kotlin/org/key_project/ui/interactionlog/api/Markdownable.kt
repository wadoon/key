package org.key_project.ui.interactionlog.api

/**
 * @author Alexander Weigl
 * @version 1 (08.05.19)
 */
interface Markdownable {
    val markdown: String
        get() = String.format("**Unsupported interaction: %s**%n%n", this.javaClass.getName())
}
