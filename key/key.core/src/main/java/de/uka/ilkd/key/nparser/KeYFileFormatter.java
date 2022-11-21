package de.uka.ilkd.key.nparser;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.Interval;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.RuleNode;
import org.antlr.v4.runtime.tree.TerminalNode;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.List;
import java.util.stream.Stream;

/* global invariant: the "cursor" is always placed at the correctly indented next position to write
 * (similar to an IDE)
 */

public class KeYFileFormatter extends KeYParserBaseVisitor<Void> {

    private static final int INDENT_STEP = 4;

    private static final boolean KEEP_ADDITIONAL_LINEBREAKS = false;
    private static final int MAX_LINES_BETWEEN = 4;

    private static final String INDENT_BUFFER = " ".repeat(100);

    StringBuilder builder = new StringBuilder();
    final CharStream cs;
    final CommonTokenStream ts;
    int currentIndentation = 0;

    public KeYFileFormatter(CharStream cs, CommonTokenStream ts) {
        this.cs = cs;
        this.ts = ts;
    }

    public static String getIndent(int count) {
        // Substrings use a shared buffer
        return INDENT_BUFFER.substring(0, count);
    }

    private void lBraceBreak(Token token) {
        builder.append('{');
        currentIndentation++;
        breakAndIndent();
        processHiddenTokensAfterCurrent(token);
    }

    private void rBrace(Token token) {
        if (currentIndentation > 0) {
            removeLastIndentationStep();
        }
        currentIndentation--;
        builder.append('}');
        processHiddenTokensAfterCurrent(token);
    }

    private void removeLastIndentationStep() {
        // sanity check
        String s = builder.substring(builder.length() - INDENT_STEP);
        if (s.chars().allMatch(c -> c == ' ')) {
            builder.delete(builder.length() - INDENT_STEP, builder.length());
        } else {
            System.out.println("Not enough indentation to delete one step...");
        }
    }

    public static String getOriginalText(ParserRuleContext ctx) {
        if (ctx.start == null || ctx.start.getStartIndex() < 0
            || ctx.stop == null || ctx.stop.getStopIndex() < 0) {
            // fallback
            return ctx.getText();
        }
        int start = ctx.start.getStartIndex();
        int end = ctx.stop.getStopIndex();
        return ctx.start.getInputStream().getText(Interval.of(start, end));
    }

    ////////////////////////////////////////////////////////////////////////////////////////////////

    @Override
    public Void visitFile(KeYParser.FileContext ctx) {
        // include prefix (comments) before the actual content
        List<Token> list = ts.getHiddenTokensToLeft(ctx.start.getTokenIndex());
        if (list != null) {
            for (Token t : list) {
                builder.append(t.getText());
            }
        }
        return super.visitFile(ctx);
    }

    @Override
    public Void visitDecls(KeYParser.DeclsContext ctx) {
        if (ctx.children != null) {
            for (int i = 0; i < ctx.children.size(); i++) {
                visit(ctx.getChild(i));
                breakAndIndent();
                breakAndIndent();
            }
        }
        return null;
    }

    @Override
    public Void visitSort_decls(KeYParser.Sort_declsContext ctx) {
        // TODO
        return super.visitSort_decls(ctx);
    }

    @Override
    public Void visitProg_var_decls(KeYParser.Prog_var_declsContext ctx) {
        // TODO
        return super.visitProg_var_decls(ctx);
    }

    @Override
    public Void visitSchema_var_decls(KeYParser.Schema_var_declsContext ctx) {
        visit(ctx.SCHEMAVARIABLES());
        space();
        lBraceBreak(ctx.LBRACE().getSymbol());

        for (int i = 0; i < ctx.one_schema_var_decl().size(); i++) {
            visit(ctx.one_schema_var_decl(i));
            visit(ctx.SEMI(i));
            breakAndIndent();
        }

        rBrace(ctx.RBRACE().getSymbol());
        return null;
    }

    @Override
    public Void visitOne_schema_var_decl(KeYParser.One_schema_var_declContext ctx) {
        if (ctx.MODALOPERATOR() != null) {
            // TODO
        } else if (ctx.PROGRAM() != null) {
            // TODO
        } else if (ctx.FORMULA() != null) {
            visit(ctx.FORMULA());
            space();
            if (ctx.schema_modifiers() != null) {
                visit(ctx.schema_modifiers());
                space();
            }
            visit(ctx.simple_ident_comma_list());
        } else if (ctx.TERMLABEL() != null) {
            // TODO
        } else if (ctx.UPDATE() != null) {
            // TODO
        } else if (ctx.SKOLEMFORMULA() != null) {
            // TODO
        } else {
            if (ctx.TERM() != null) {
                visit(ctx.TERM());
            } else if (ctx.VARIABLES() != null) {
                visit(ctx.VARIABLES());
            } else if (ctx.VARIABLE() != null) {
                visit(ctx.VARIABLE());
            } else if (ctx.SKOLEMTERM() != null) {
                visit(ctx.SKOLEMTERM());
            }
            space();
            if (ctx.schema_modifiers() != null) {
                visit(ctx.schema_modifiers());
                space();
            }
            visit(ctx.sortId());
            space();
            visit(ctx.simple_ident_comma_list());
        }

        return null;
    }

    @Override
    public Void visitSimple_ident_comma_list(KeYParser.Simple_ident_comma_listContext ctx) {
        visit(ctx.simple_ident(0));
        for (int i = 1; i < ctx.simple_ident().size(); i++) {
            visit(ctx.COMMA(i - 1));
            space();
            visit(ctx.simple_ident(i));
        }
        return null;
    }

    @Override
    public Void visitPred_decls(KeYParser.Pred_declsContext ctx) {
        // TODO
        return super.visitPred_decls(ctx);
    }

    @Override
    public Void visitFunc_decls(KeYParser.Func_declsContext ctx) {
        // TODO
        return super.visitFunc_decls(ctx);
    }

    @Override
    public Void visitTransform_decls(KeYParser.Transform_declsContext ctx) {
        // TODO
        return super.visitTransform_decls(ctx);
    }

    @Override
    public Void visitRuleset_decls(KeYParser.Ruleset_declsContext ctx) {
        // TODO
        return super.visitRuleset_decls(ctx);
    }

    @Override
    public Void visitRulesOrAxioms(KeYParser.RulesOrAxiomsContext ctx) {
        if (ctx.DOC_COMMENT() != null) {
            visit(ctx.DOC_COMMENT());
            breakAndIndent();
        }
        if (ctx.RULES() != null) {
            visit(ctx.RULES());
        } else if (ctx.AXIOMS() != null) {
            visit(ctx.AXIOMS());
        }
        if (ctx.option_list() != null) {
            visit(ctx.option_list());
        }
        space();

        lBraceBreak(ctx.LBRACE().getSymbol());

        for (int i = 0; i < ctx.taclet().size(); i++) {
            visit(ctx.taclet(i));
            visit(ctx.SEMI(i));
            breakAndIndent();
        }
        rBrace(ctx.RBRACE().getSymbol());

        return null;
    }

    private void visitChildren(RuleNode node, int startOffset) {
        int n = node.getChildCount();
        for (int i = startOffset; i < n; i++) {
            ParseTree c = node.getChild(i);
            c.accept(this);
        }
    }

    @Override
    public Void visitGoalspecs(KeYParser.GoalspecsContext ctx) {
        for (int i = 0; i < ctx.goalspecwithoption().size(); i++) {
            visit(ctx.goalspecwithoption(i));
            var semi = ctx.SEMI(i);
            if (semi != null) {
                visit(semi);
            }
            breakAndIndent();
        }
        return null;
    }

    @Override
    public Void visitGoalspec(KeYParser.GoalspecContext ctx) {
        int firstChild = 0;
        if (ctx.name != null) {
            visit(ctx.name);
            builder.append(": ");
            // TODO new line and indent?
            currentIndentation++;
            breakAndIndent();
            firstChild = 2;
        }

        visitChildren(ctx, firstChild);
        if (ctx.name != null) {
            currentIndentation--;
        }
        return null;
    }

    @Override
    public Void visitModifiers(KeYParser.ModifiersContext ctx) {
        for (int i = 0; i < ctx.getChildCount(); i++) {
            visit(ctx.getChild(i));
            breakAndIndent();
        }
        return null;
    }

    @Override
    public Void visitVarexplist(KeYParser.VarexplistContext ctx) {
        var varexps = ctx.varexp();
        var commas = ctx.COMMA();
        boolean multiline = varexps.size() > 3;
        if (multiline) {
            breakAndIndent();
        }
        for (int i = 0; i < varexps.size(); i++) {
            visit(varexps.get(i));
            if (i < commas.size()) {
                visit(commas.get(i));
                if (multiline) {
                    breakAndIndent();
                } else {
                    space();
                }
            }
        }
        return null;
    }

    @Override
    public Void visitTaclet(KeYParser.TacletContext ctx) {
        if (ctx.DOC_COMMENT() != null) {
            visit(ctx.DOC_COMMENT());
            breakAndIndent();
        }
        if (ctx.LEMMA() != null) {
            visit(ctx.LEMMA());
            breakAndIndent();
        }
        visit(ctx.IDENT());
        space();
        if (ctx.option_list() != null) {
            visit(ctx.option_list());
            space();
        }
        lBraceBreak(ctx.LBRACE().getSymbol());

        // schemaVarDecls
        for (int i = 0; i < ctx.one_schema_var_decl().size(); i++) {
            visit(ctx.SCHEMAVAR(i));
            space();
            visit(ctx.one_schema_var_decl(i));
            visit(ctx.SEMI(i));
            breakAndIndent();
        }

        int parenCounter = 0;   // necessary to be able to process the correct hidden tokens

        // assumes
        if (ctx.ifSeq != null) {
            visit(ctx.ASSUMES());
            visit(ctx.LPAREN(0));
            visit(ctx.ifSeq);
            visit(ctx.RPAREN(0));
            breakAndIndent();
            parenCounter++;
        }

        if (ctx.find != null) {
            visit(ctx.FIND());
            visit(ctx.LPAREN(parenCounter));
            visit(ctx.find);
            visit(ctx.RPAREN(parenCounter));
            breakAndIndent();

            // visit further polarity restrictions etc.
            int polaritiesEtc = ctx.SAMEUPDATELEVEL().size() + ctx.INSEQUENTSTATE().size()
                + ctx.ANTECEDENTPOLARITY().size() + ctx.SUCCEDENTPOLARITY().size();
            int first = 0;
            while (ctx.getChild(first) != ctx.find) {
                first++;
            }
            first++;
            first++;
            for (int i = first; i < first + polaritiesEtc; i++) {
                visit(ctx.getChild(i));
            }

            breakAndIndent();
        }

        // varconds
        for (int i = 0; i < ctx.varexplist().size(); i++) {
            visit(ctx.VARCOND(i));
            builder.append("(");
            currentIndentation++;
            visit(ctx.varexplist(i));
            builder.append(")");
            currentIndentation--;
            breakAndIndent();
        }

        visit(ctx.goalspecs());
        visit(ctx.modifiers());

        rBrace(ctx.RBRACE().getSymbol());

        return null;
    }
    ////////////////////////////////////////////////////////////////////////////////////////////////

    private void breakAndIndent() {
        builder.append('\n');
        builder.append(getIndent(INDENT_STEP * currentIndentation));
    }

    private void space() {
        builder.append(' ');
    }

    private void processHiddenTokensAfterCurrent(Token currentToken) {
        // add hidden tokens after the current token (whitespace, comments etc.)
        List<Token> list = ts.getHiddenTokensToRight(currentToken.getTokenIndex());
        if (list != null) {
            for (Token t : list) {
                String text = t.getText();
                if (t.getType() == KeYLexer.WS) {
                    int nls = countNLs(text) - 1;
                    for (int k = 0; k < Math.min(nls, MAX_LINES_BETWEEN); k++) {
                        breakAndIndent();
                    }
                    /*if (nls > 0) {
                        int i = currentIndentation;
                        int cur = currentToken.getTokenIndex();
                        if (cur < ts.size() - 1) {
                            int nextTy = ts.get(cur + 1).getType();
                            if (nextTy == KeYLexer.RPAREN || nextTy == KeYLexer.RBRACE)
                                i--;
                        }
                        text = multi(nls, "\n") + multi(INDENT_STEP * i, " ");
                        builder.append(text);
                    }*/
                } else if (t.getType() == KeYLexer.SL_COMMENT) {    // TODO: other comment types
                    processIndentationInSLComment(t);
                } else {
                    builder.append(text);
                }
//                builder.append(t.getText());
            }
        }
    }

    private void processIndentationInSLComment(Token t) {
        String text = t.getText();
        // Normalize actual comment content
        if (text.startsWith("//")) {
            text = text.substring(2);
            builder.append("// ");
        }
        builder.append(text.trim());
        breakAndIndent();
    }

    @Override
    public Void visitTerminal(TerminalNode node) {
        //builder.append(node.getText());

        /*if (node.getSymbol().getTokenIndex() == KeYLexer.LBRACE) {
            currentIndentation++;
        } else if (node.getSymbol().getTokenIndex() == KeYLexer.RBRACE) {
            currentIndentation--;
        }*/
        if (node.getSymbol().getType() == KeYLexer.LPAREN) {
            currentIndentation++;
        } else if (node.getSymbol().getType() == KeYLexer.RPAREN) {
            if (currentIndentation == 0) {
                throw new IllegalStateException("Unmatched closing RPAREN.");
            }
            currentIndentation--;
        }

        String str = node.getSymbol().getText();
        builder.append(str);

        processHiddenTokensAfterCurrent(node.getSymbol());
        return super.visitTerminal(node);
    }

    private static int countNLs(String text) {
        return (int) text.chars().filter(x -> x == '\n').count();
    }

    public static void main(String[] args) throws IOException {
        String dirname = "/home/wolfram/Desktop/tmp/rules";
        Path ruleDir = Paths.get(dirname);
        formatDirectory(ruleDir);
    }

    private static void formatDirectory(Path dir) throws IOException {
        Path outDir = dir.getParent().resolve("output");
        outDir.toFile().mkdirs();
        try (Stream<Path> s = Files.list(dir)) {
            s.forEach(p -> {
                try {
                    formatSingleFile(dir.resolve(p.getFileName()), outDir, true);
                } catch (IOException e) {
                    throw new RuntimeException(e);
                }
            });
        }
    }

    private static String formatFile(CharStream in) {
        KeYLexer lexer = new KeYLexer(in);
        lexer.setTokenFactory(new CommonTokenFactory(true));

//        KeYLexer lexer2 = ParsingFacade.createLexer(p);

        CommonTokenStream tokens = new CommonTokenStream(lexer);
        tokens.fill();
        //CommonTokenStream hidden = new CommonTokenStream(lexer, KeYLexer.HIDDEN);
        KeYParser parser = new KeYParser(tokens);
        KeYParser.FileContext ctx = parser.file();
        KeYFileFormatter formatter = new KeYFileFormatter(in, tokens);
        formatter.visitFile(ctx);
        return formatter.builder.toString();
    }

    private static void formatSingleFile(Path input, Path outDir, boolean overwrite) throws IOException {
        final String nameExt = input.getFileName().toString();
        final String filename = nameExt.substring(0, nameExt.length() - 4);
        final String extension = ".key";
        var content = Files.readString(input).replaceAll("\\r\\n?", "\n");
        var formatted = formatFile(CharStreams.fromString(content));

        Path output = outDir.resolve(filename + extension);
        if (Files.exists(output) && !overwrite) {
            output = Files.createTempFile(outDir, filename, extension);
        }
        var newlineReplaced = formatted.replaceAll("\n", System.lineSeparator());
        Files.writeString(output, newlineReplaced);
    }
}
