package de.uka.ilkd.key.gui.smt;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;

public class SMTResultOutput {
    static final String TIMEOUT = "TO";
    static final String COUNTEREXAMPLE = "CE";
    static final String UNKNOWN = "UK";
    static final String EXCEPTION = "EXC";
    static final String USER_INTERRUPT = "USR_IR";
    static final String TOP_ROW = "GOAL_ID,SOLVER,RESULT";

    private final Path path = Paths.get("smtResults.csv");
    private BufferedWriter buf;

    SMTResultOutput() {
        String s = path.toAbsolutePath().toString();
        System.out.println("Current relative path is: " + s);
        System.out.println("Path: " + path);
        try {
            buf = new BufferedWriter(new FileWriter(path.toFile()));
            buf.write(TOP_ROW);
            buf.newLine();
        } catch (IOException e) {
            System.out.println("Could not open file " + path);
        }
    }

    void appendLine(String s) {
        try {
            buf.write(s);
            buf.newLine();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public void close() {
        try {
            buf.flush();
            buf.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

}
