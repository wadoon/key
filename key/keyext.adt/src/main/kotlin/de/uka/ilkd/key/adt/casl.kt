package de.uka.ilkd.key.adt;

import de.uka.ilkd.key.adt.ADTLangLexer
import de.uka.ilkd.key.adt.ADTLangParser
import de.uka.ilkd.key.adt.CaslLexer
import de.uka.ilkd.key.adt.CaslParser
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream

/**
 *
 * @author Alexander Weigl
 * @version 1 (5/20/21)
 */
object CaslFrontend {
    fun parse(filename: String): CaslParser.Spec_defnContext {
        val lexer = CaslLexer(CharStreams.fromFileName(filename))
        val parser = CaslParser(CommonTokenStream(lexer))
        val ctx = parser.spec_defn()
        require(parser.numberOfSyntaxErrors == 0)
        return ctx
    }
}