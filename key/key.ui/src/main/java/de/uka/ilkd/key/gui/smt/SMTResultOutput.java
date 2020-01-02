package de.uka.ilkd.key.gui.smt;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;

public class SMTResultOutput {
    static final String VALID = "VALID";
    static final String TIMEOUT = "TO";
    static final String COUNTEREXAMPLE = "CE";
    static final String UNKNOWN = "UK";
    static final String EXCEPTION = "EXC";
    static final String USER_INTERRUPT = "USR_IR";

    private BufferedWriter buf;

    private ArrayList<String> goalRows;
    private ArrayList<String> solverColumns;
    private ArrayList<ArrayList<Result>> results;

    SMTResultOutput() {
        Path path = Paths.get("smtResults.csv");
        String s = path.toAbsolutePath().toString();
        goalRows = new ArrayList<>();
        solverColumns = new ArrayList<>();
        results = new ArrayList<>();
        try {
            buf = new BufferedWriter(new FileWriter(path.toFile()));
        } catch (IOException e) {
            System.out.println("Could not open file " + path);
        }
    }

    void addResult(String goalID, String solverName, Result result) {
        if (!goalRows.contains(goalID)) {
            goalRows.add(goalID);
            results.add(new ArrayList<>());
        }
        if (!solverColumns.contains(solverName)) {
            solverColumns.add(solverName);
        }
        results.get(goalRows.indexOf(goalID)).add(result);
    }

    public void close() {
        try {
            writeColumnHeads();
            for (int i = 0; i < goalRows.size(); ++i) {
                buf.write(goalRows.get(i));
                for (int j = 0; j < solverColumns.size(); ++j) {
                    buf.write("," + results.get(i).get(j));
                }
                buf.newLine();
            }
            buf.flush();
            buf.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private void writeColumnHeads() {
        try {
            buf.write("Goal ID");
            for (String s: solverColumns) {
                buf.write("," + s + " (Result)");
                buf.write("," + s + " (Time)");
            }
            buf.newLine();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    static class Result {

        String result;
        String time;

        public Result(String result, String time) {
            this.result = result;
            this.time = time;
        }

        public Result(String result) {
            this.result = result;
            this.time = "";
        }

        public Result() {
            this.result = "";
            this.time = "";
        }

        public String toString() {
            return result + "," + time;
        }
    }

}
