package de.uka.ilkd.key.njml;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Token;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.key_project.util.collection.ImmutableSLList;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (5/15/20)
 */
@RunWith(Parameterized.class)
public class ContractTranslatorTest {
    @Parameterized.Parameter(value = 0)
    public String expr = "";

    @Parameterized.Parameters(name = "{0}")
    public static Collection<Object[]> getFiles() throws IOException {
        List<Object[]> seq = new LinkedList<>();
        try (InputStream s = ExpressionTranslatorTest.class.getResourceAsStream("contracts.txt");
             BufferedReader reader = new BufferedReader(new InputStreamReader(s))) {
            String l;
            StringBuilder content = new StringBuilder();
            while ((l = reader.readLine()) != null) {
                System.out.println(l);
                if (l.trim().isEmpty() || l.startsWith("#"))
                    continue;
                content.append(l).append('\n');
            }
            final String[] split = content.toString().split("---Contract---");
            for (String value : split) {
                value = value.trim();
                if (!value.isEmpty())
                    seq.add(new Object[]{value.replaceAll("---Contract---", "")});
            }
        }
        return seq;
    }

    private Recoder2KeY r2k;
    private Services services;

    @Before
    public void setup() {
        if (services != null) return;
        services = TacletForTests.services();
        r2k = new Recoder2KeY(services, services.getNamespaces());
        r2k.parseSpecialClasses();
    }

    @Test
    public void parseAndInterpret() throws SLTranslationException {
        System.out.println(expr);
        Assert.assertNotEquals("", expr);
        KeYJavaType kjt = new KeYJavaType(Sort.ANY);
        ProgramVariable self = new LocationVariable(new ProgramElementName("self"), kjt);
        ProgramVariable result = new LocationVariable(new ProgramElementName("result"), kjt);
        ProgramVariable exc = new LocationVariable(new ProgramElementName("exc"), kjt);
        JmlLexer lexer = JmlFacade.createLexer(expr);
        JmlParser parser = new JmlParser(new CommonTokenStream(lexer));
        JmlParser.Method_specificationContext ctx = parser.method_specification();
        if (parser.getNumberOfSyntaxErrors() != 0)
            debugLexer();
        Assert.assertEquals(0, parser.getNumberOfSyntaxErrors());
        ExpressionTranslator et = new ExpressionTranslator(services, kjt, self, ImmutableSLList.nil(), result, exc,
                new HashMap<>(), new HashMap<>());
        JMLSpecFactory2 factory = new JMLSpecFactory2(services, et);
        ContractTranslator ct = new ContractTranslator("", new Position(0,0), factory, kjt);
        System.out.println(ctx.accept(ct));
    }

    private void debugLexer() {
        JmlLexer lexer = JmlFacade.createLexer(expr);
        Token tok;
        do {
            int modeBefore = lexer._mode;
            tok = lexer.nextToken();
            boolean sTl = lexer.semicolonOnToplevel();
            System.out.println(sTl);
            System.out.printf("(%3d) %15s %25s [%d->%d]\n",
                    tok.getType(), lexer.getVocabulary().getDisplayName(tok.getType()), tok.getText(), modeBefore, lexer._mode);
        } while (tok.getType() != -1);
    }
}