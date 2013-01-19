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
package de.uni_freiburg.informatik.ultimate.smtinterpol;

import java.io.File;
import java.math.BigInteger;

/**
 * Generic interface for the different parsers of SMTInterpol. Each interface (SMTLIB, SMTLIB 2,
 * DIMACS,...) should provide an implementation of this interface to be used by the generic main
 * method.
 * 
 * @author Juergen Christ
 */
public interface IParser {

    /**
     * Parse a specific file. This sets the basic options configurable from command line. Note that
     * a value of <code>null</code> is legal with the intended meaning of a noop. If the filename is
     * <code>null</code>, the parser should parse standard input,
     * 
     * @param verbosity
     *            The verbosity to set.
     * @param timeout
     *            The timeout to set.
     * @param seed
     *            The random seed to set.
     * @param filename
     *            The name of the file to parse.
     * @return Exit code.
     */
    public int run(
            BigInteger verbosity,
            BigInteger timeout,
            BigInteger seed,
            String filename);

    public int run(BigInteger verbosity, BigInteger timeout, BigInteger seed, File file);
}
