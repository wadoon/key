package de.uka.ilkd.key.parser.njava;

import de.uka.ilkd.key.java.recoderext.ProofJavaProgramFactory;
import org.antlr.v4.runtime.CharStreams;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import recoder.ParserException;
import recoder.java.CompilationUnit;
import recoder.java.PrettyPrinter;
import recoder.java.SourceElement;

import java.io.*;
import java.util.*;

/**
 * @author Alexander Weigl
 * @version 1 (10/15/20)
 */
@RunWith(Parameterized.class)
public class RegressionTest {
    private static Properties p = new Properties();

    static {
        p.setProperty("indentationAmount", "4");
        p.setProperty("overwriteIndentation", "true");
        p.setProperty("overwriteParsePositions", "true");
        p.setProperty("glueParameterLists", "false");
        p.setProperty("glueParameters", "false");
        p.setProperty("glueControlExpressions", "false");
        p.setProperty("glueExpressionParentheses", "false");
    }

    @Parameterized.Parameters
    public static Collection<Object[]> readJava() {
        return readFile("/java.txt");
    }

    static Collection<Object[]> readFile(String s) {
        InputStream in = RegressionTest.class.getResourceAsStream(s);
        HashSet<String> got = new HashSet<>();
        Collection<Object[]> seq = new ArrayList<>();
        try (BufferedReader br = new BufferedReader(new InputStreamReader(in))) {
            String tmp;
            String type = null;
            StringBuilder cur = new StringBuilder();
            while ((tmp = br.readLine()) != null) {
                if (tmp.startsWith("====")) {
                    type = tmp.substring(5).trim();
                } else if (tmp.equals("----")) {
                    final String java = cur.toString().trim();
                    if (!got.contains(java)) {
                        seq.add(new Object[]{type, java});
                        got.add(java);
                    }
                    cur = new StringBuilder();
                } else {
                    cur.append("\n").append(tmp);
                }
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
        return seq;
    }

    private final ProofJavaProgramFactory factory = (ProofJavaProgramFactory) ProofJavaProgramFactory.getInstance();

    @Parameterized.Parameter(0)
    public String type;
    @Parameterized.Parameter(1)
    public String content;


    @Test
    public void parse() throws ParserException, IOException {
        SourceElement expected = null, actual = null;
        System.out.println(content);

        switch (type) {
            case "compilationUnit":
                expected = factory.parseCompilationUnit(content);
                ((CompilationUnit) expected).setComments(null);
                actual = JavaParserFacade.parseCompilationUnit(CharStreams.fromString(content));
                break;
            case "field":
                expected = factory.parseFieldDeclaration(content);
                actual = JavaParserFacade.parseFieldDeclaration(CharStreams.fromString(content));
                break;
            case "member":
                expected = factory.parseMemberDeclaration(content);
                actual = JavaParserFacade.parseMemberDeclaration(CharStreams.fromString(content));
                break;
            case "method":
                expected = factory.parseMemberDeclaration(content);
                actual = JavaParserFacade.parseMethodDeclaration(CharStreams.fromString(content));
                break;
            case "block":
                expected = factory.parseStatementBlock(new StringReader(content));
                actual = JavaParserFacade.parseStatementBlock(CharStreams.fromString(content));
                break;
            default:
                //TODO
        }
        if (!Objects.equals(expected, actual)) {
            /*PrettyPrinter pp = new PP(new OutputStreamWriter(System.out), p);
            expected.accept(pp);
            actual.accept(pp);*/
            Assert.fail();
        }
    }
}

class PP extends PrettyPrinter {
    public PP(Writer out, Properties props) {
        super(out, props);
    }
}