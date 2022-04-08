package de.uka.ilkd.key.casl.parser;

import org.antlr.v4.runtime.BailErrorStrategy;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.ConsoleErrorListener;
import org.antlr.v4.runtime.DiagnosticErrorListener;
import org.antlr.v4.runtime.atn.PredictionMode;
import org.antlr.v4.runtime.tree.ErrorNode;

import java.io.IOException;
import java.nio.file.Path;
import java.util.LinkedList;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;

public class CaslParser {
    private static final Logger LOGGER = Logger.getLogger(CaslParser.class.getName());


    public static CASLParser createParser(Path file) throws IOException {
        CharStream charStream = CharStreams.fromPath(file);
        return createParser(charStream);
    }

    public static CASLParser createParser(String casl) {
        CharStream charStream = CharStreams.fromString(casl);
        return createParser(charStream);
    }

    public static CASLParser createParser(CharStream casl) {
        return createParser(casl, false);
    }

    public static CASLParser createParser(CharStream casl, boolean diagnostics) {
        CASLLexer lexer = new CASLLexer(casl);
        CommonTokenStream stream = new CommonTokenStream(lexer);
        CASLParser caslParser = new CASLParser(stream);

        caslParser.getInterpreter().setPredictionMode(PredictionMode.LL_EXACT_AMBIG_DETECTION);
        caslParser.setErrorHandler(new BailErrorStrategy());
        caslParser.removeErrorListeners();
        if (diagnostics) {
            caslParser.addErrorListener(new DiagnosticErrorListener());
        }
        caslParser.addErrorListener(ConsoleErrorListener.INSTANCE);

        return caslParser;
    }

    public static class ErrorListener extends CASLParserBaseListener {
        private static final Logger LOGGER = Logger.getLogger(ErrorListener.class.getName());
        static {
            Logger.getLogger("de.uka.ilkd.key.casl").setLevel(Level.ALL);
        }

        public final List<ErrorNode> errorList = new LinkedList<>();

        @Override
        public void visitErrorNode(ErrorNode node) {
            errorList.add(node);
        }
    }
}
