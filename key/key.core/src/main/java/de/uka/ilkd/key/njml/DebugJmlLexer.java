package de.uka.ilkd.key.njml;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonToken;
import org.antlr.v4.runtime.Token;

import java.io.*;
import java.util.*;
import java.util.stream.Collectors;

/**
 * This program is a little for debugging KeY Lexer.
 * <p>
 * You can start this problem via gradle:
 * <code>
 * <pre>
 * gradle debugLexer
 * </pre>
 * </code>
 * <p>
 * This program ask for input, lexes it and shows the found token.
 *
 * @author weigl
 * @version 2019-12-09
 */
public class DebugJmlLexer {
    private static final String DEFAULT_FORMAT = "%02d %20s %d:%-50s\n";
    private final PrintStream stream;
    private final String format;
    private final Collection<JmlLexer> lexer;

    public DebugJmlLexer(PrintStream stream, String format, Collection<JmlLexer> lexer) {
        this.stream = stream;
        this.format = format;
        this.lexer = lexer;
    }

    public DebugJmlLexer(List<File> files) {
        stream = System.out;
        lexer = files.stream().map(it -> {
            try {
                return JmlFacade.createLexer(CharStreams.fromPath(it.toPath()));
            } catch (IOException e) {
                e.printStackTrace(stream);
            }
            return null;
        }).filter(Objects::nonNull)
                .collect(Collectors.toList());
        format = DEFAULT_FORMAT;
    }

    public static void main(String[] args) {
        if (args.length > 0) {
            new DebugJmlLexer(
                    Arrays.stream(args).map(File::new).collect(Collectors.toList())).run();
        } else {
            try (BufferedReader input = new BufferedReader(new InputStreamReader(System.in))) {
                String tmp;
                do {
                    System.out.print(">>> ");
                    tmp = input.readLine();
                    if (tmp != null) {
                        debug(tmp);
                    } else {
                        break;
                    }
                }
                while (true);
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    public static void debug(String content) {
        debug(JmlFacade.createLexer(CharStreams.fromString(content)));
    }

    public static void debug(JmlLexer lexer) {
        DebugJmlLexer dkl = new DebugJmlLexer(System.out, DEFAULT_FORMAT, Collections.singleton(lexer));
        dkl.run();
    }

    public void run() {
        for (JmlLexer l : lexer)
            run(l);
    }

    private void run(JmlLexer toks) {
        Token t;
        do {
            t = toks.nextToken();
            stream.format(format,
                    toks.getLine(),
                    toks.getVocabulary().getSymbolicName(t.getType()),
                    toks._mode,
                    t.getText().replace("\n", "\\n"));
            //if (t.getType() == JmlLexer.ERROR_CHAR) stream.println("!!ERROR!!");
        } while (t.getType() != CommonToken.EOF);
    }
}