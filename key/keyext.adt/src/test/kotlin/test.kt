package de.uka.ilkd.key.adt

import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.DynamicTest.dynamicTest
import org.junit.jupiter.api.TestFactory
import java.io.File
import java.util.stream.Stream
import kotlin.streams.asStream

/**
 *
 * @author Alexander Weigl
 * @version 1 (5/20/21)
 */
class AdtFileTests {
    @TestFactory
    fun a(): Stream<DynamicTest> {
        val s = File("src/test/resources/adtexamples").absoluteFile
        require(s.exists()) { "Folder $s not found" }

        println(s)
        val files = s.listFiles()

        require(files!=null && files.isNotEmpty())

        return files.asSequence().map {
            dynamicTest(it.name) {
                CaslFrontend.parse(it.absolutePath)
            }
        }.asStream() ?: Stream.empty()
    }
}