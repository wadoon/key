package org.key_project.ui.interactionlog.algo

import org.key_project.ui.interactionlog.api.Interaction
import org.key_project.ui.interactionlog.model.InteractionLog
import org.key_project.ui.interactionlog.model.NodeInteraction
import java.io.PrintWriter
import java.io.StringWriter

/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */
open class MUProofScriptExport {
    companion object {
        fun writeTo(logbook: InteractionLog, writer: PrintWriter) {
            writer.format("// Proof script: *%s*%n", logbook.name)
            writer.format("// Created at *%s*%n", logbook.created)
            logbook.interactions.forEach({ it ->
                writeSelector(writer, it)
                writer.write(it.proofScriptRepresentation)
            })
        }

        private fun writeSelector(out: PrintWriter, it: Interaction) {
            try {
                (it as NodeInteraction).nodeId?.let {
                    out.format("select %s;%n", it.branchLabel)
                }
            } catch (ignored: ClassCastException) {
            }
        }

        fun getScript(current: InteractionLog): String {
            val sw = StringWriter()
            writeTo(current, PrintWriter(sw))
            return sw.toString()
        }
    }
}
