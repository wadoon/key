package de.uka.ilkd.key.parser.njava;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Recoder2KeYConverter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.recoderext.ProofJavaProgramFactory;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.init.JavaProfile;
import org.antlr.v4.runtime.CharStreams;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import recoder.ParserException;
import recoder.java.CompilationUnit;
import recoder.java.JavaProgramElement;
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
    static FileWriter fwActual;
    static FileWriter fwExpected;
    static {
        try {
            fwActual = new FileWriter("/tmp/a.txt");
            fwExpected = new FileWriter("/tmp/b.txt");
            Runtime.getRuntime().addShutdownHook(new Thread(() -> {
                try {
                    fwExpected.close();
                } catch (IOException e) {
                    e.printStackTrace();
                }
                try {
                    fwActual.close();
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }));
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    @Parameterized.Parameters
    public static Collection<Object[]> readJava() {
        return readFile("/java.txt");
    }

    public static Collection<Object[]> readFile(String s) {
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
            Services services = new Services(new JavaProfile());
            Recoder2KeY rec2key = new Recoder2KeY(services, services.getNamespaces());
            Recoder2KeYConverter r2k = new Recoder2KeYConverter(rec2key, services, services.getNamespaces());
            ProgramElement keyExpected = r2k.convert((JavaProgramElement)expected);

            fwExpected.write("===\n");
            new ProgramPrinter(fwExpected).printProgramElementName((ProgramElementName) keyExpected);
            fwExpected.write("===\n");

            ProgramElement keyActual = r2k.convert((JavaProgramElement)actual);
            fwActual.write("===\n");
            ProgramPrinter p = new ProgramPrinter(fwActual);
            p.printProgramElementName((ProgramElementName) keyActual);
            fwActual.write("===\n");

            //PrettyPrinter pp = new PP(new OutputStreamWriter(System.out), p);
            //expected.accept(pp);
            //actual.accept(pp);
        if (!Objects.equals(fwExpected, fwActual)) {
            Assert.fail();
        }
    }
}
