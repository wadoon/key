package org.key_project.editor.java;

import edu.key_project.editor.java.JavaJMLLexer;
import edu.key_project.editor.java.JavaJMLParser;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.ATNConfigSet;
import org.antlr.v4.runtime.dfa.DFA;
import org.fife.io.DocumentReader;
import org.fife.ui.rsyntaxtextarea.RSyntaxDocument;
import org.fife.ui.rsyntaxtextarea.parser.AbstractParser;
import org.fife.ui.rsyntaxtextarea.parser.DefaultParseResult;
import org.fife.ui.rsyntaxtextarea.parser.DefaultParserNotice;
import org.fife.ui.rsyntaxtextarea.parser.ParseResult;

import java.io.IOException;
import java.util.BitSet;

public class JavaJMLLinter extends AbstractParser implements ANTLRErrorListener {
    private DefaultParseResult result = new DefaultParseResult(this);

    @Override
    public ParseResult parse(RSyntaxDocument doc, String style) {
        result.clearNotices();
        DocumentReader reader = new DocumentReader(doc);
        try {
            JavaJMLLexer lexer = new JavaJMLLexer(CharStreams.fromReader(reader));
            JavaJMLParser parser = new JavaJMLParser(new CommonTokenStream(lexer));
            parser.removeErrorListeners();
            parser.addErrorListener(this);
            lexer.addErrorListener(this);
            JavaJMLParser.CompilationUnitContext ctx = parser.compilationUnit();
        } catch (IOException e) {
            e.printStackTrace();
        }
        return result;
    }

    @Override
    public void syntaxError(Recognizer<?, ?> recognizer, Object offendingSymbol,
                            int line, int charPositionInLine, String msg, RecognitionException e) {
        try {
            Token t = (Token) offendingSymbol;
            result.addNotice(new DefaultParserNotice(this, msg, line, t.getStartIndex(),
                    t.getStopIndex() - t.getStartIndex() + 1));
        } catch (ClassCastException e1) {
            e1.printStackTrace();
        }
    }

    @Override
    public void reportAmbiguity(Parser recognizer, DFA dfa, int startIndex, int stopIndex, boolean exact, BitSet ambigAlts, ATNConfigSet configs) {

    }

    @Override
    public void reportAttemptingFullContext(Parser recognizer, DFA dfa, int startIndex, int stopIndex, BitSet conflictingAlts, ATNConfigSet configs) {

    }

    @Override
    public void reportContextSensitivity(Parser recognizer, DFA dfa, int startIndex, int stopIndex, int prediction, ATNConfigSet configs) {

    }
}
