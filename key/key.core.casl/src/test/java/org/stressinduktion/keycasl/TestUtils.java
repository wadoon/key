package org.stressinduktion.keycasl;

import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeWalker;
import org.junit.jupiter.api.Assertions;
import org.stressinduktion.keycasl.parser.CaslParser;

public class TestUtils {
    public static void testParser(ParseTree tree) {
        CaslParser.ErrorListener errorListener = new CaslParser.ErrorListener();
        ParseTreeWalker.DEFAULT.walk(errorListener, tree);
        Assertions.assertTrue(errorListener.errorList.isEmpty());
    }
}
