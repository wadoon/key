package de.uka.ilkd.key.parser.njava;

import de.uka.ilkd.key.nparser.JavaKParser;
import org.antlr.v4.runtime.CharStreams;
import org.junit.Test;

import java.io.IOException;
import java.io.InputStream;

/**
 * @author Alexander Weigl
 * @version 1 (10/12/20)
 */
public class JavaParserFacadeTest {
    @Test
    public void testAllInOne7() throws IOException {
        InputStream is = getClass().getResourceAsStream("/de/uka/ilkd/key/AllInOne7.java");
        JavaKParser.CompilationUnitContext ctx = JavaParserFacade.parseFile(CharStreams.fromStream(is));
        JavaKBuilder b = new JavaKBuilder();
        ctx.accept(b);
    }

    @Test
    public void testAllInOne8() throws IOException {
        InputStream is = getClass().getResourceAsStream("/de/uka/ilkd/key/AllInOne8.java");
        JavaKParser.CompilationUnitContext ctx = JavaParserFacade.parseFile(CharStreams.fromStream(is));
        JavaKBuilder b = new JavaKBuilder();
        ctx.accept(b);
    }
}