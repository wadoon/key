/*
 * Copyright (C) 2009-2012 University of Freiburg
 * 
 * This file is part of SMTInterpol.
 * 
 * SMTInterpol is free software: you can redistribute it and/or modify it under the terms of the GNU
 * Lesser General Public License as published by the Free Software Foundation, either version 3 of
 * the License, or (at your option) any later version.
 * 
 * SMTInterpol is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without
 * even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License along with SMTInterpol.
 * If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

import java.io.File;
import java.math.BigInteger;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.smtinterpol.IParser;

public class SMTLIB2Parser
        implements IParser {

    @Override
    public int run(
            BigInteger verbosity,
            BigInteger timeout,
            BigInteger seed,
            String filename) {

        // TODO Auto-generated method stub
        if (filename == null)
            filename = "<stdin>";
        SMTInterpol solver = new SMTInterpol(Logger.getRootLogger(), true);
        if (verbosity != null)
            solver.setOption(":verbosity", verbosity);
        if (timeout != null)
            solver.setOption(":timeout", timeout);
        if (seed != null)
            solver.setOption(":random-seed", seed);
        ParseEnvironment parseEnv = new ParseEnvironment(solver);
        parseEnv.parseScript(filename);
        return 0;
    }

    @Override
    public int run(BigInteger verbosity, BigInteger timeout, BigInteger seed, File file) {

        SMTInterpol solver = new SMTInterpol(Logger.getRootLogger(), true);
        if (verbosity != null)
            solver.setOption(":verbosity", verbosity);
        if (timeout != null)
            solver.setOption(":timeout", timeout);
        if (seed != null)
            solver.setOption(":random-seed", seed);
        ParseEnvironment parseEnv = new ParseEnvironment(solver);
        parseEnv.parseScript(file);
        return 0;
    }

}
