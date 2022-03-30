package org.stressinduktion.keycasl.parser;

import org.antlr.v4.runtime.ParserRuleContext;
import org.stressinduktion.keycasl.main.Util;

import java.util.logging.Logger;

public class CaslError {
    private static final Logger LOGGER = Util.getLogger(CaslError.class);

    static class UnsupportedException extends RuntimeException {
        UnsupportedException(String msg) {
            super(msg);
        }
    }

    public static <T> T unsupported(String what, ParserRuleContext ctx) {
        LOGGER.warning(() -> String.format("%s: \"%s\"", what, ctx.getText()));
        throw new UnsupportedException(what);
    }

    public static <T> T error(String text, ParserRuleContext ctx) {
        LOGGER.severe(() -> String.format("%s", text));
        throw new RuntimeException(text);
    }
}
