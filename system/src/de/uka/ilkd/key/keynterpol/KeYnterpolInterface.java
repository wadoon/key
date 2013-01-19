package de.uka.ilkd.key.keynterpol;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.math.BigInteger;
import java.util.Scanner;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.smt.SmtLib2Translator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Bridge;
import de.uni_freiburg.informatik.ultimate.smtinterpol.IParser;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Main;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTLIB2Parser;

/**
 * The primary interface between KeY and SMTInterpol. Very experimental for now, just wanting to
 * find out what we can do with it.
 * 
 * @author christopher
 */
public class KeYnterpolInterface {

    public static void main(String[] args) throws IOException {

        /*
         * Setup the pseduo file holding the SMTLib script (to avoid messing too much with the
         * parser internals for now.
         */
        File file = new File("hej");
        FileWriter writer = new FileWriter(file);
        writer.write("(set-option :print-success false)\n" + "(set-logic QF_LIA)\n"
                + "(declare-fun x () Int)\n" + "(declare-fun y () Int)\n"
                + "(assert (! (> x y) :named IP_0))\n"
                + "(assert (! (= x 0) :named IP_1))\n"
                + "(assert (! (> y 0) :named IP_2))\n" + "(check-sat)\n" + "(exit)");
        writer.close();

        /*
         * Invoke the SMTLib parser and see what happens. TODO: Need to redirect output from stdout
         * to filestream.
         */
        run(null, null, null, file);
    }

    public static void run(
            BigInteger verbosity,
            BigInteger timeout,
            BigInteger seed,
            File file) {

        IParser parser = new SMTLIB2Parser();

        int exitCode = parser.run(verbosity, timeout, seed, file);
        System.exit(exitCode);
    }

    /**
     * Translates a {@link Term} instance to a corresponding SMTLIB-2 proof obligation.
     * 
     * @param term
     */
    private void translateTerm(Term term) {

    }
}
