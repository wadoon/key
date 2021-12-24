package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.recoderext.adt.EmptyMapLiteral;
import de.uka.ilkd.key.java.recoderext.adt.EmptySeqLiteral;
import de.uka.ilkd.key.java.recoderext.adt.EmptySetLiteral;
import de.uka.ilkd.key.parser.proofjava.ParseException;
import de.uka.ilkd.key.parser.proofjava.ProofJavaParser;
import de.uka.ilkd.key.util.HelperClassForTests;
import org.junit.Assert;
import org.junit.Test;
import recoder.java.Expression;

import java.io.StringReader;

/**
 * @author Alexander Weigl
 * @version 1 (12/24/21)
 */
public class EscapeJavaTests {
    final Services services = HelperClassForTests.createServices();
    final Recoder2KeY r2k = new Recoder2KeY(services, services.getNamespaces());

    private Expression readExpression(String expr) throws ParseException {
        synchronized (ProofJavaParser.class) {
            ProofJavaParser.initialize(new StringReader(expr));
            return ProofJavaParser.Expression();
        }
    }

    @Test
    public void testAdtLiterals() throws ParseException {
        Assert.assertTrue(readExpression("\\empty") instanceof EmptySetLiteral);
        Assert.assertTrue(readExpression("\\seq_empty") instanceof EmptySeqLiteral);
        Assert.assertTrue(readExpression("\\map_empty") instanceof EmptyMapLiteral);
    }


    @Test
    public void testEscapeAdtConstructors() throws ParseException {
        Expression expr = readExpression("\\seq_get(\\seq_empty, 5)");
        System.out.println(expr);
        "{ result = s.equals(obj); }"
    }
}
