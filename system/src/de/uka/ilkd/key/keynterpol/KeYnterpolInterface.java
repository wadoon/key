package de.uka.ilkd.key.keynterpol;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.smtinterpol.IParser;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTLIB2Parser;

/**
 * The primary interface between KeY and SMTInterpol. Very experimental for now, just wanting to
 * find out what we can do with it.
 * 
 * @author christopher
 */
public enum KeYnterpolInterface {
    INSTANCE;

    /**
     * Execute SMTInterpol with the given parameters.
     * 
     * @param verbosity
     *            the verbosity of the output from the solver.
     * @param timeout
     *            timeout settings for the solver.
     * @param seed
     *            random seed for this session.
     * @param commands
     *            the SMTLIB2 commands to run.
     * @return the output of the solver.
     */
    public static String run(
            BigInteger verbosity,
            BigInteger timeout,
            BigInteger seed,
            String commands) {

        IParser parser = new SMTLIB2Parser();

        int exitCode = parser.runCommands(verbosity, timeout, seed, commands);

        if (exitCode == 0) {
            return "";
        }
        else {
            return "ERROR";
        }
    }
}
