package de.uni_freiburg.informatik.ultimate.smtinterpol;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTLIB2Parser;

public class Bridge {

    public static void run(BigInteger verbosity, BigInteger timeout, BigInteger seed, File file) {

        IParser parser = new SMTLIB2Parser();

        int exitCode = parser.run(verbosity, timeout, seed, file);
        System.exit(exitCode);
    }

    public static void main(String[] args) throws IOException {

        /**
         * Bridge to SMTinterpol
         */
        Bridge bridge = new Bridge();

        /*
         * Setup the pseduo file holding the SMTLib script (to avoid messing too much with the
         * parser internals for now.
         */
        File file = new File("random");
        FileWriter writer = new FileWriter(file);
        writer.write("Hej");
        writer.close();

        /*
         * Invoke the SMTLib parser and see what happens.
         */
        bridge.run(null, null, null, file);
    }
}
