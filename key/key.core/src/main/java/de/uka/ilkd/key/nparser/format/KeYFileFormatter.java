package de.uka.ilkd.key.nparser.format;

import de.uka.ilkd.key.nparser.KeYLexer;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.KeYParserBaseVisitor;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.RuleNode;
import org.antlr.v4.runtime.tree.TerminalNode;

import javax.annotation.Nullable;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class KeYFileFormatter extends KeYParserBaseVisitor<Void> {
    private static final int MAX_LINES_BETWEEN = 3;

    final Output output = new Output();
    final CommonTokenStream ts;

    public KeYFileFormatter(CommonTokenStream ts) {
        this.ts = ts;
    }

    ////////////////////////////////////////////////////////////////////////////////////////////////

    @Override
    public Void visitFile(KeYParser.FileContext ctx) {
        // include prefix (comments) before the actual content
        processHiddenTokens(ts.getHiddenTokensToLeft(ctx.start.getTokenIndex()), output);
        return super.visitFile(ctx);
    }

    @Override
    public Void visitTerm(KeYParser.TermContext ctx) {
        return new ExpressionVisitor(ts, output).visitTerm(ctx);
    }

    @Override
    public Void visitOption_list(KeYParser.Option_listContext ctx) {
        output.noSpaceBeforeNext();
        return new ExpressionVisitor(ts, output).visitOption_list(ctx);
    }

    @Override
    public Void visitSchema_var_decls(KeYParser.Schema_var_declsContext ctx) {
        for (int i = 0; i < ctx.getChildCount(); i++) {
            var child = ctx.getChild(i);
            if (child instanceof TerminalNode) {
                var token = ((TerminalNode) child).getSymbol().getType();
                if (token == KeYParser.SCHEMAVARIABLES) {
                    output.assertNewLineAndIndent();
                } else if (token == KeYParser.RBRACE) {
                    visit(child);
                    output.assertNewLine();
                    continue;
                }
            }
            visit(child);
        }

        return null;
    }

    @Override
    public Void visitRulesOrAxioms(KeYParser.RulesOrAxiomsContext ctx) {
        for (int i = 0; i < ctx.getChildCount(); i++) {
            var child = ctx.getChild(i);
            if (child instanceof TerminalNode) {
                var token = ((TerminalNode) child).getSymbol().getType();
                if (token == KeYParser.DOC_COMMENT ||
                        token == KeYParser.RULES ||
                        token == KeYParser.AXIOMS) {
                    output.assertNewLineAndIndent();
                } else if (token == KeYParser.RBRACE) {
                    visit(child);
                    output.assertNewLine();
                    continue;
                }
            }
            visit(child);
        }
        return null;
    }

    private void visitChildren(RuleNode node, int startOffset, int endOffset) {
        for (int i = startOffset; i < endOffset; i++) {
            ParseTree c = node.getChild(i);
            c.accept(this);
        }
    }

    @Override
    public Void visitGoalspec(KeYParser.GoalspecContext ctx) {
        int firstChild = 0;
        output.assertNewLineAndIndent();
        if (ctx.name != null) {
            visit(ctx.name);
            visit(ctx.COLON());
            output.spaceBeforeNext();
            output.enterIndent();
            output.assertNewLineAndIndent();
            firstChild = 2;
        }

        visitChildren(ctx, firstChild, ctx.getChildCount());
        if (ctx.name != null) {
            output.exitIndent();
        }
        return null;
    }

    @Override
    public Void visitModifiers(KeYParser.ModifiersContext ctx) {
        for (int i = 0; i < ctx.getChildCount(); i++) {
            var child = ctx.getChild(i);
            if (child instanceof TerminalNode) {
                var token = ((TerminalNode) child).getSymbol().getType();
                if (token == KeYParser.NONINTERACTIVE) {
                    output.assertNewLineAndIndent();
                    visit(child);
                    continue;
                }

                if (token == KeYParser.DISPLAYNAME || token == KeYParser.HELPTEXT) {
                    output.assertNewLineAndIndent();
                    visit(child);
                    output.spaceBeforeNext();
                    continue;
                }
            }
            visit(child);
        }
        return null;
    }

    @Override
    public Void visitVarexplist(KeYParser.VarexplistContext ctx) {
        var varexps = ctx.varexp();
        var commas = ctx.COMMA();
        boolean multiline = varexps.size() > 3;
        for (int i = 0; i < varexps.size(); i++) {
            if (multiline) {
                output.assertNewLineAndIndent();
            }
            visit(varexps.get(i));
            if (i < commas.size()) {
                visit(commas.get(i));
                if (!multiline && output.isNewLine()) {
                    multiline = true;
                }
            }
        }
        return null;
    }

    @Override
    public Void visitOne_include_statement(KeYParser.One_include_statementContext ctx) {
        output.assertNewLineAndIndent();
        output.enterIndent();
        super.visitOne_include_statement(ctx);
        output.exitIndent();
        return null;
    }

    @Override
    public Void visitTaclet(KeYParser.TacletContext ctx) {
        var n = ctx.getChildCount();
        for (int i = 0; i < n; ++i) {
            var child = ctx.getChild(i);
            if (child instanceof TerminalNode) {
                var token = ((TerminalNode) child).getSymbol().getType();
                if (token == KeYLexer.DOC_COMMENT ||
                        token == KeYLexer.LEMMA ||
                        token == KeYLexer.IDENT ||
                        token == KeYLexer.ASSUMES ||
                        token == KeYLexer.FIND ||
                        token == KeYLexer.SAMEUPDATELEVEL ||
                        token == KeYLexer.ANTECEDENTPOLARITY ||
                        token == KeYLexer.SUCCEDENTPOLARITY ||
                        token == KeYLexer.INSEQUENTSTATE ||
                        token == KeYLexer.VARCOND) {
                    output.assertNewLineAndIndent();
                } else if (token == KeYParser.SCHEMAVAR) {
                    output.assertNewLineAndIndent();
                    visit(child);
                    output.spaceBeforeNext();
                    continue;
                } else if (token == KeYLexer.RBRACE) {
                    output.assertNewLine();
                }
            } else if (child instanceof RuleContext) {
                if (child instanceof KeYParser.Option_listContext) {
                    output.spaceBeforeNext();
                }
            }

            visit(child);
        }

        return null;
    }
    ////////////////////////////////////////////////////////////////////////////////////////////////

    static void processHiddenTokens(@Nullable List<Token> tokens, Output output) {
        if (tokens == null) {
            return;
        }

        for (Token t : tokens) {
            String text = t.getText();
            if (t.getType() == KeYLexer.WS) {
                int nls = countNLs(text);
                for (int k = 0; k < Math.min(nls, MAX_LINES_BETWEEN); k++) {
                    output.newLine();
                }
            } else {
                var normalized = text.replaceAll("\t", Output.getIndent(1));
                if (t.getType() == KeYLexer.SL_COMMENT) {
                    processIndentationInSLComment(normalized, output);
                } else if (t.getType() == KeYLexer.COMMENT_END) {
                    processIndentationInMLComment(normalized, output);
                } else {
                    throw new IllegalStateException("unexpected hidden token type " + t.getType());
                }
            }
        }
    }

    static void processHiddenTokensAfterCurrent(Token currentToken, CommonTokenStream ts,
            Output output) {
        // add hidden tokens after the current token (whitespace, comments etc.)
        List<Token> list = ts.getHiddenTokensToRight(currentToken.getTokenIndex());
        processHiddenTokens(list, output);
    }

    static void processIndentationInMLComment(String text, Output output) {
        // Normalize and split
        var lines = text.split("\n");

        // Find minimal indent shared among all lines except the first
        // Doc like comments start with * in every line except the first
        int minIndent = Integer.MAX_VALUE;
        boolean isDocLike = true;
        for (int i = 1; i < lines.length; ++i) {
            var line = lines[i];
            var stripped = line.stripLeading();
            // Empty lines are ignored for this
            if (!stripped.isEmpty()) {
                minIndent = Math.min(minIndent, line.length() - stripped.length());
                isDocLike &= stripped.startsWith("*");
            }
        }

        // Remove /* and */
        lines[0] = lines[0].substring(2).stripLeading();
        var lastLine = lines[lines.length - 1];
        lines[lines.length - 1] = lastLine.substring(0, lastLine.length() - 2);

        output.token("/*");
        // Skip space if we start with another *, e.g. /**
        if (!lines[0].startsWith("*") && !lines[0].startsWith("!")) {
            output.spaceBeforeNext();
        }
        for (int i = 0; i < lines.length; i++) {
            String line = lines[i];
            if (i != 0) {
                // Watch out for empty line when removing the common indent
                line = line.isEmpty() ? line : line.substring(minIndent);
            } else {
                line = line.stripLeading();
            }
            line = line.stripTrailing();

            // Print nonempty line
            if (!line.isEmpty()) {
                output.assertIndented();
                if (isDocLike && i != 0) {
                    output.spaceBeforeNext();
                }
                output.token(line);
            }
            if (i != lines.length - 1) {
                output.newLine();
            } else {
                // Add space for doc like comments
                if (isDocLike && !line.endsWith("*")) {
                    output.assertIndented();
                    output.spaceBeforeNext();
                }
            }
        }

        output.token("*/");
        output.spaceBeforeNext();
    }

    static void processIndentationInSLComment(String text, Output output) {
        output.assertNewLineAndIndent();
        var trimmed = text.stripTrailing();
        // Normalize actual comment content
        if (trimmed.startsWith("//")) {
            trimmed = trimmed.substring(2);
            output.token("//");
            if (!trimmed.startsWith(" ") && !trimmed.startsWith("/")) {
                output.spaceBeforeNext();
            }
        }
        if (!trimmed.isEmpty()) {
            output.token(trimmed);
        }
        output.newLine();
    }

    @Override
    public Void visitTerminal(TerminalNode node) {
        var token = node.getSymbol().getType();

        boolean isLBrace =
            token == KeYLexer.LBRACE || token == KeYLexer.LPAREN || token == KeYLexer.LBRACKET;
        if (isLBrace) {
            output.spaceBeforeNext();
        } else if (token == KeYLexer.RBRACE || token == KeYLexer.RPAREN
                || token == KeYLexer.RBRACKET) {
            output.noSpaceBeforeNext();
            output.exitIndent();
        }

        if (token == KeYLexer.AVOID || token == KeYLexer.SEQARROW) {
            output.spaceBeforeNext();
        }

        var noSpaceAround =
            token == KeYLexer.COLON || token == KeYLexer.DOT || token == KeYLexer.DOUBLECOLON;
        var noSpaceBefore =
            token == KeYLexer.SEMI || token == KeYLexer.COMMA || token == KeYLexer.LPAREN;
        if (noSpaceBefore || noSpaceAround) {
            output.noSpaceBeforeNext();
        }

        String text = node.getSymbol().getText();
        if (token == KeYLexer.DOC_COMMENT) {
            processIndentationInMLComment(text, output);
        } else {
            output.token(text);
        }

        if (isLBrace) {
            output.enterIndent();
        }

        if (!(isLBrace || noSpaceAround)) {
            output.spaceBeforeNext();
        }

        processHiddenTokensAfterCurrent(node.getSymbol(), ts, output);
        return super.visitTerminal(node);
    }

    private static int countNLs(String text) {
        return (int) text.chars().filter(x -> x == '\n').count();
    }

    /**
     * Entry level method to the formatter.
     * The formatter uses System.lineSeparator as line separator and accepts any line separator as
     * input.
     *
     * @param text the input text
     * @return the formatted text *or null*, if the input was not parseable
     */
    public static @Nullable String format(String text) {
        var in = CharStreams.fromString(text.replaceAll("\\r\\n?", "\n"));
        KeYLexer lexer = new KeYLexer(in);
        lexer.setTokenFactory(new CommonTokenFactory(true));

        CommonTokenStream tokens = new CommonTokenStream(lexer);
        tokens.fill();

        KeYParser parser = new KeYParser(tokens);
        KeYParser.FileContext ctx = parser.file();
        if (parser.getNumberOfSyntaxErrors() > 0) {
            return null;
        }

        KeYFileFormatter formatter = new KeYFileFormatter(tokens);
        formatter.visitFile(ctx);
        var formatted = formatter.output.toString().trim() + "\n";
        return formatted.replaceAll("\n", System.lineSeparator());
    }

    ////// Test functions below //////

    private static void formatSingleFile(Path input, Path output) throws IOException {
        var content = Files.readString(input);
        var formatted = format(content);

        if (formatted == null) {
            System.err.println("Failed to format " + input);
            return;
        }

        if (!formatted.equals(format(formatted))) {
            System.err.println("Formatter is not convergent on " + input);
        }

        var noWhitespaceContent = content.replaceAll("\\s+", "");
        var noWhitespaceFormatted = formatted.replaceAll("\\s+", "");
        if (!noWhitespaceContent.equals(noWhitespaceFormatted)) {
            System.err.println("File changed: " + input);
        }

        Files.writeString(output, formatted);
    }

    private static void formatSingleFileInSameDir(Path input) throws IOException {
        var fileName = input.getFileName().toString();
        if (!fileName.endsWith(".key")) {
            System.err.println("Ignoring non key file " + input);
            return;
        }
        var stem = fileName.substring(0, fileName.length() - 4);
        var output = input.resolveSibling(stem + ".format.key");
        formatSingleFile(input, output);
    }

    private static void formatSingleFileTo(Path input, Path outputDir) throws IOException {
        var output = outputDir.resolve(input.getFileName());
        formatSingleFile(input, output);
    }

    @SuppressWarnings("unused")
    private static void formatDirectoryTest(Path dir) throws IOException {
        Path outDir = dir.getParent().resolve("output");
        // noinspection ResultOfMethodCallIgnored
        outDir.toFile().mkdirs();
        try (Stream<Path> s = Files.list(dir)) {
            s.forEach(p -> {
                var file = dir.resolve(p.getFileName());
                try {
                    var name = file.getFileName().toString();
                    if (name.endsWith(".format.format.key")) {
                        // noinspection ResultOfMethodCallIgnored
                        file.toFile().delete();
                        return;
                    }
                    formatSingleFileInSameDir(file);
                    if (!name.endsWith(".format.key")) {
                        formatSingleFileTo(file, outDir);
                    }
                } catch (Exception e) {
                    System.err.println("Exception while processing " + file);
                    throw new RuntimeException(e);
                }
            });
        }
    }

    private static boolean formatOrCheckInPlace(Path file, boolean format) {
        try {
            var content = Files.readString(file);
            var formatted = format(content);
            if (formatted == null) {
                System.err.println("Failed to format " + file);
                return false;
            }

            var differs = !content.equals(formatted);
            if (differs) {
                if (format) {
                    Files.writeString(file, formatted);
                } else {
                    System.err.println(file + " is not formatted correctly");
                    return false;
                }
            }
        } catch (Exception e) {
            System.err.println("Exception while processing " + file);
            e.printStackTrace();
            return false;
        }
        return true;
    }

    public static void main(String[] args) throws IOException {
        if (args.length != 2 || (!args[0].equals("format") && !args[0].equals("check"))) {
            System.err.println("Usage:");
            System.err.println("* format a directory or a file: format <path>");
            System.err.println("* check a directory or a file: check <path>");
            System.exit(3);
            return;
        }

        var format = args[0].equals("format");
        var path = Paths.get(args[1]);
        var file = path.toFile();
        if (!file.exists()) {
            System.err.println("Input path does not exist");
            System.exit(2);
            return;
        }

        List<Path> files;
        if (file.isDirectory()) {
            try (Stream<Path> s = Files.list(path)) {
                files = s.collect(Collectors.toList());
            }
        } else {
            files = Collections.singletonList(path);
        }

        var valid = true;
        for (Path f : files) {
            valid &= formatOrCheckInPlace(f, format);
        }

        if (!valid) {
            System.exit(1);
        }
    }
}
