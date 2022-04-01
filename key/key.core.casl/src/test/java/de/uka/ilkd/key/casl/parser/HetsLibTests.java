package de.uka.ilkd.key.casl.parser;

import de.uka.ilkd.key.casl.TestUtils;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;

import java.io.IOException;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.stream.Stream;

@Disabled
public class HetsLibTests {
    private static final Logger LOGGER = Logger.getLogger(HetsLibTests.class.getName());
    static {
        LOGGER.setLevel(Level.ALL);
    }

    private static void testParser(Path caslPath) throws IOException {
        LOGGER.info(() -> String.format("Testing Hets-lib CASL file \"%s\".", caslPath.getFileName()));
        CASLParser parser = CaslParser.createParser(caslPath);
        CASLParser.Lib_defn_eofContext lib_defn_eofContext = parser.lib_defn_eof();
        TestUtils.testParser(lib_defn_eofContext);
    }

    @TestFactory
    Stream<DynamicTest> testHetsLib() throws IOException, URISyntaxException {
        Set<String> nonWorking = Set.of("StructuredDatatypes.casl");
        Path corpus = Path.of(this.getClass().getResource("casl-corpus").toURI());
        return Files.list(corpus)
                .filter(path -> path.getFileName().toString().endsWith(".casl"))
                .filter(path -> !nonWorking.contains(path.getFileName().toString()))
                .sorted()
                .map(path -> DynamicTest.dynamicTest(
                        path.getFileName().toString(),
                        () -> {
                            Assumptions.assumeFalse(nonWorking.contains(path.getFileName().toString()));
                            testParser(path);
                        }));
    }
}
