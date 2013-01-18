/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib;

import java.io.FileReader;
import java.io.InputStreamReader;
import java.io.Reader;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.MySymbolFactory;



public class Main {
	private static void usage() {
		System.err.println("USAGE smtinterpol [-q] [-v] [-t <num>] [-c <file>] [-d] [file.smt]");
	}
	
	public static void main(String[] param) throws Exception {
		int verbosity = 4;
        int timeout = 0;
        int paramctr = 0;
        String conversionFile = null;
        boolean disableIPol = false;
        while (paramctr < param.length
        		&& param[paramctr].startsWith("-")) {
        	if (param[paramctr].equals("--")) {
        		paramctr++;
        		break;
        	} else if (param[paramctr].equals("-v")) {
        		verbosity = 5;
        		paramctr++;
        	} else if (param[paramctr].equals("-q")) {
        		verbosity = 2;
        		paramctr++;
        	} else if (param[paramctr].equals("-t") && 
        			++paramctr < param.length) {
        		try {
        			timeout = Integer.parseInt(param[paramctr]);
        			if (timeout < 0) {
        				timeout = 0;
        				System.err.println("Cannot parse timeout " +
        						"argument: Negative number");
        			}
        		} catch (NumberFormatException nfe) {
        			System.err.println("Cannot parse timeout " +
        					"argument: Not a number");
        		}
        		paramctr++;
        	} else if (param[paramctr].equals("-c") && 
        			++paramctr < param.length) {
       			conversionFile = param[paramctr++];
        	} else if (param[paramctr].equals("-d")) {
        		disableIPol = true;
        	} else {
        		usage();
        		return;
        	}
        }
		MySymbolFactory symfactory = new MySymbolFactory();
		Reader reader;
		String filename;
		if (paramctr < param.length) {
			filename = param[paramctr++];
			reader = new FileReader(filename);
		} else {
			filename = "<stdin>";
			reader = new InputStreamReader(System.in);
		}
		if (paramctr != param.length) {
			usage();
			return;
		}
		Lexer lexer = new Lexer(reader);
		lexer.setSymbolFactory(symfactory);
		Parser parser = new Parser(lexer, symfactory);
		parser.setFileName(filename);
		parser.open(conversionFile, disableIPol);
		if (verbosity != 4)
			parser.benchmark.setOption(":verbosity", verbosity);
		if (timeout > 0)
			parser.benchmark.setOption(":timeout", BigInteger.valueOf(timeout));
		parser.parse();
		Term[] interpolants = parser.benchmark.check();
		if (interpolants != null) {
			for (int i = 0; i < interpolants.length; ++i)
				System.out.println("Interpolant "+i+": "+interpolants[i]);
		}
		parser.benchmark.close();
	}
}
