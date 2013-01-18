package de.uka.ilkd.key.keynterpol;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Scanner;

import de.uni_freiburg.informatik.ultimate.smtinterpol.Bridge;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Main;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

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

        Main.main(new String[] { "hej" });

        /*
         * Invoke the SMTLib parser and see what happens.
         */
        Bridge.run(null, null, null, file);

        file.delete();
    }
}
