package de.uka.ilkd.key.parser.njava;

import de.uka.ilkd.key.nparser.JavaKLexer;
import de.uka.ilkd.key.nparser.JavaKParser;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;

/**
 * @author Alexander Weigl
 * @version 1 (10/12/20)
 */
public class JavaParserFacade {
    public static  JavaKParser.CompilationUnitContext parseFile(CharStream stream) {
        return createParser(stream).compilationUnit();
    }

    public static JavaKParser createParser(CharStream stream) {
        JavaKParser parser = new JavaKParser(new CommonTokenStream(createLexer(stream)));
        return parser;
    }

    public static JavaKLexer createLexer(CharStream stream) {
        JavaKLexer lexer = new JavaKLexer(stream);
        return lexer;
    }
}
