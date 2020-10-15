package de.uka.ilkd.key.parser.njava;

import de.uka.ilkd.key.java.recoderext.ProofJavaProgramFactory;
import de.uka.ilkd.key.java.recoderext.SchemaJavaProgramFactory;
import org.antlr.v4.runtime.CharStreams;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import recoder.ParserException;
import recoder.java.SourceElement;

import java.io.*;
import java.util.Collection;
import java.util.TreeSet;

/**
 * @author Alexander Weigl
 * @version 1 (10/15/20)
 */
@RunWith(Parameterized.class)
public class SchemaRegressionTest {
    @Parameterized.Parameters
    public static Collection<Object[]> readJava() {
        return RegressionTest.readFile("/schema.txt");
    }

    private final SchemaJavaProgramFactory factory = (SchemaJavaProgramFactory) SchemaJavaProgramFactory.getInstance();

    @Parameterized.Parameter(0)
    public String type;
    @Parameterized.Parameter(1)
    public String content;


    @Test
    public void parse() throws ParserException, IOException {
        SourceElement expected = null, actual = null;
        switch (type) {
            case "compilationUnit":
                expected = factory.parseCompilationUnit(content);
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
                assert false;
        }
        Assert.assertEquals(expected, actual);
    }
}