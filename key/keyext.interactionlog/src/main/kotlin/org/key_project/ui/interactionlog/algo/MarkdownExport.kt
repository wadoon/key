package org.key_project.ui.interactionlog.algo

import org.key_project.ui.interactionlog.api.Markdownable
import org.key_project.ui.interactionlog.api.Interaction
import org.key_project.ui.interactionlog.model.InteractionLog
import org.key_project.ui.interactionlog.Markdown

import java.io.PrintWriter

class MarkdownExport(private val writer: PrintWriter) {
    companion object {

        fun writeTo(logbook: InteractionLog, writer: PrintWriter) {
            val me = MarkdownExport(writer)
            writer.format("# Log book *%s*%n%n", logbook.name)
            writer.format("Created at *%s*%n%n", logbook.created)
            logbook.interactions.forEach({ it -> writer.format(getMarkdown(it) + "\n") })
        }

        fun getMarkdown(interaction: Interaction): String {
            try {
                val m = interaction as Markdownable
                return m.markdown
            } catch (e: ClassCastException) {
            }

            return ""
        }

        fun getHtml(inter: Interaction): String {
            return Markdown.html(getMarkdown(inter))
        }
    }
}
