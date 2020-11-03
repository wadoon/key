import edu.key_project.editor.java.JavaJMLLexer;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.Token;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.key_project.util.helper.FindResources;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.StringWriter;
import java.util.LinkedList;
import java.util.List;
import java.util.Objects;

/**
 * @author Alexander Weigl
 * @version 1 (01.08.19)
 */
@RunWith(Parameterized.class)
public class JavaLexerTest {
    @Parameterized.Parameter(0)
    public File javaFile;

    @Parameterized.Parameter(1)
    public File tokFile;

    @Parameterized.Parameters(name = "{0}")
    public static List<Object[]> arguments() {
        List<Object[]> tests = new LinkedList<>();
        final File file = new File(FindResources.getTestResourcesDirectory(), "javaLexerTests");
        for (File f : Objects.requireNonNull(file.listFiles())) {
            if (f.getName().endsWith(".java"))
                tests.add(new Object[]{f, new File(f.getParentFile(), f.getName() + ".tokens")});
        }
        return tests;
    }


    @Test
    public void test() throws IOException {
        JavaJMLLexer lexer = new JavaJMLLexer(CharStreams.fromPath(javaFile.toPath()));
        StringWriter sw = new StringWriter();
        Token t = lexer.nextToken();
        while (t.getType() != JavaJMLLexer.EOF) {
            sw.write(String.format("%25s : %-20s : %5s%n",
                    t.getText().replace("\n", "\\n")
                            .replaceAll("\t", "\\t"),
                    lexer.getVocabulary().getSymbolicName(t.getType()),
                    lexer.getModeNames()[lexer._mode]
            ));
            t = lexer.nextToken();
        }
        String actual = sw.toString();
        try (FileWriter in = new FileWriter(new File(javaFile.getParentFile(),
                javaFile.getName() + ".actualtokens"))) {
            in.write(actual);
            in.flush();
        } catch (Exception ignored) {
        }

        //String expected = Files.asCharSource(tokFile, StandardCharsets.UTF_8).read();
        //Assert.assertEquals(expected, actual);
    }
}
