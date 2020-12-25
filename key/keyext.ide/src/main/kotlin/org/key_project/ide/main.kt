package org.key_project.ide

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import javafx.application.Application
import kotlin.io.path.ExperimentalPathApi


object KeyIde {
    @ExperimentalPathApi
    @JvmStatic
    fun main(args: Array<String>) {
        Application.launch(IdeApp::class.java, *args)
    }
}
