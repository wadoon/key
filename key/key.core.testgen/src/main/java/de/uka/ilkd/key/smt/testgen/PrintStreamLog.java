package de.uka.ilkd.key.smt.testgen;

import java.io.PrintStream;

/**
 * @author Alexander Weigl
 * @version 1 (12/12/20)
 */
public class PrintStreamLog implements TestGenerationLog {
    private final PrintStream out;

    public PrintStreamLog(PrintStream out) {
        this.out = out;
    }

    @Override
    public void writeln(String string) {
        out.println(string);
    }

    @Override
    public void write(String string) {
        out.print(string);
    }

    @Override
    public void writeException(Throwable t) {
        t.printStackTrace(out);
    }

    @Override
    public void testGenerationCompleted() {
        writeln("Completed");
    }
}
