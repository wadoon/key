import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.nparser.ParsingFacade;
import org.antlr.v4.runtime.CharStreams;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestFactory;
import org.key_project.key.tptp.Facade;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.stream.Stream;

public class TestTptp {
    @TestFactory
    public Stream<DynamicTest> tests() throws IOException {
        return Files.walk(Paths.get("./src/test/resources/"))
                .filter(it -> it.toString().endsWith(".tptp"))
                .map(it -> DynamicTest.dynamicTest(it.toString(), () -> test(it)));
    }

    private void test(Path tptp) throws IOException {
        StringWriter sw = new StringWriter();
        Facade.translateTptpFile(tptp, new PrintWriter(sw));
        var actual = sw.toString();
        var name = tptp.toString().replace(".tptp", ".key");
        System.out.println(actual);
        ParsingFacade.parseFile(CharStreams.fromString(actual));

        var expected = Files.readString(Paths.get(name));
        Assertions.assertEquals(expected, actual);
    }
}
