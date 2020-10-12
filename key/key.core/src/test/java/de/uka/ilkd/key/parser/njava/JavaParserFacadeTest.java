package de.uka.ilkd.key.parser.njava;

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
        JavaParserFacade.parseFile(CharStreams.fromStream(is));
    }

    @Test
    public void testAllInOne8() throws IOException {
        InputStream is = getClass().getResourceAsStream("/de/uka/ilkd/key/AllInOne8.java");
        JavaParserFacade.parseFile(CharStreams.fromStream(is));
    }
}