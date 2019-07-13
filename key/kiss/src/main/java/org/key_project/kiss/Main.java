package org.key_project.kiss;

import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.macros.scripts.ScriptLineLexer;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import org.jetbrains.annotations.NotNull;
import org.jline.reader.*;
import org.jline.terminal.Terminal;
import org.jline.terminal.TerminalBuilder;
import org.jline.utils.AttributedString;
import org.jline.utils.Colors;

import java.io.*;
import java.util.List;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingDeque;

/**
 * Key interactive script shell.
 *
 * @author weigl
 */
public class Main {
    private static final RuntimeException proofClosedException = new RuntimeException();


    public static void main(String[] args) throws ProblemLoaderException, InterruptedException, ScriptException, IOException {
        if (args.length != 1) {
            System.out.println("Usage: ./kiss <file.proof>");
            System.exit(1);
        }

        KeYEnvironment<?> env = KeYEnvironment.load(new File(args[0]));
        Proof proof = env.getLoadedProof();
        try {
            System.out.println(">>> Proof loaded. Waiting for commands");
            runShell(proof);
        } finally {
            env.dispose(); // Ensure always that all instances of KeYEnvironment are disposed
        }
    }

    private static void runShell(Proof proof) throws InterruptedException, ScriptException, IOException {
        Reader reader = getReader();
        /*int c = 0;
        while ((c = reader.read()) != -1) {
            System.out.println((char) c);
        }*/

        ProofScriptEngine pse = new ProofScriptEngine(reader,
                new Location("<interactive>", -1, -1)) {
            @Override
            protected void afterCommandApplication(ProofScriptCommand<Object> command, Object arg, Node firstNode) {
                if (proof.closed()) {
                    throw proofClosedException;
                }
            }
        };
        try {
            pse.execute(new DefaultUserInterfaceControl(), proof);
        } catch (ScriptException e) {
            if (e.getCause() != proofClosedException) {
                throw e;
            } else {
                System.out.println("Proof is closed");
            }

        }
    }

    @NotNull
    private static Reader getReader() {
        try {
            Terminal terminal = TerminalBuilder.terminal();

            LineReader lineReader = LineReaderBuilder.builder()
                    .terminal(terminal)
                    .completer(new MyCompleter())
                    //.highlighter(new MyHighlighter())
                    //.parser(new MyParser())
                    .build();

            final StringReaderInteractive p = new StringReaderInteractive();
            Thread t = new Thread(() -> {
                final Writer writer = p.asWriter();
                while (true) {
                    try {
                        try {
                            String in = lineReader.readLine(">>> ");
                            writer.write(in);
                        } catch (EndOfFileException | UserInterruptException e) {
                            writer.write(-1);
                            System.exit(0);
                        }
                    } catch (IOException e) {
                        e.printStackTrace();
                    }
                }
            });
            t.setDaemon(true);
            t.start();
            return p.asReader();
        } catch (Exception e) {
            return new InputStreamReader(System.in);
        }
    }

    private static class MyHighlighter implements Highlighter {
        @Override
        public AttributedString highlight(LineReader reader, String buffer) {
            AttributedString as = new AttributedString(buffer);
            ScriptLineLexer lexer = new ScriptLineLexer();
            for (int i = 0; i < buffer.length(); i++)
                lexer.feed(buffer.charAt(i));
            for (ScriptLineLexer.Token t : lexer.fetchAllAndClear()) {
                for (int s = t.pos; s < (t.pos + t.text.length()) && s < buffer.length(); s++) {
                    as.styleAt(s).foreground(
                            t.type == ScriptLineLexer.TokenType.ID ? Colors.rgbColor("blue")
                                    : t.type == ScriptLineLexer.TokenType.STRING ? Colors.rgbColor("green")
                                    : 0
                    );
                }
            }
            return as;
        }
    }
}

class StringReaderInteractive {
    private BlockingQueue<Character> buffer = new LinkedBlockingDeque<>(10000);

    public Reader asReader() {
        class MyReader extends Reader {
            @Override
            public synchronized int read(@NotNull char[] cbuf, int off, int len) {
                int readed = 0;
                try {
                    for (int i = 0; i < off; i++) {
                        buffer.take();
                    }

                    for (int i = 0; i < len; i++) {
                        cbuf[i] = buffer.take();
                        ++readed;
                        if (cbuf[i] == (char) -1) {
                            break;
                        }
                    }
                } catch (InterruptedException e) {
                    e.printStackTrace();
                }
                return readed;
            }

            @Override
            public void close() {
                buffer.clear();
            }
        }
        return new MyReader();
    }

    public Writer asWriter() {
        class MyWriter extends Writer {
            @Override
            public void write(@NotNull char[] cbuf, int off, int len) {
                for (int i = off; i < len; i++) {
                    buffer.offer(cbuf[i]);
                }
            }

            @Override
            public void flush() {
            }

            @Override
            public void close() {
            }
        }
        return new MyWriter();
    }
}

class MyCompleter implements Completer {
    @Override
    public void complete(LineReader reader, ParsedLine line, List<Candidate> candidates) {
        try {
            if (line.line().isBlank()) {
                KeYApi.getScriptCommandApi().getScriptCommands().forEach(it -> {
                    candidates.add(new Candidate(it.getName()));
                });
            } else {
                KeYApi.getScriptCommandApi().getScriptCommands(line.words().get(0))
                        .getArguments().forEach(it -> candidates.add(new Candidate(it.getName())));
            }
        } catch (Exception e) {

        }
    }
}