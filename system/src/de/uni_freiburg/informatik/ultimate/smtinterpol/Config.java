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
package de.uni_freiburg.informatik.ultimate.smtinterpol;

import org.apache.log4j.Level;

/**
 * Basic configuration of SMTInterpol.
 * @author Juergen Christ
 */
public interface Config {

	/// Competition mode
	public final static boolean COMPETITION = false;
	
	////// General configuration
	/// Create timing statistics
	public final static boolean PROFILE_TIME = !COMPETITION;
	/// Default log level
	public final static Level DEFAULT_LOG_LEVEL = COMPETITION ? Level.ERROR : Level.INFO;
	/// Check the status set by the user against our check-sat status
	public final static boolean CHECK_STATUS_SET = !COMPETITION;
	
	////// DPLL configuration
	/// Activity limit
	public final static double LIMIT = 1e250;
	/// Unlearn clauses with activity below this threshold
	public final static double CLAUSE_UNLEARN_ACTIVITY = 1e-150;
	/// Activity factor for atoms
	public final static double ATOM_ACTIVITY_FACTOR = 1.1;
	/// Activity factor for clauses
	public final static double CLS_ACTIVITY_FACTOR = 1.01;
	/// Backtrack as far as possible
	public final static boolean DEEP_BACKTRACK = true;
	/// When to restart
	public final static int RESTART_FACTOR = 500;
	/// Use an unknown initial random seed (introduces nondeterminism)
	public final static boolean UNKNOWN_SEED = false;
	/// The default random seed
	public final static long RANDOM_SEED = 11350294L;// Currently delays random splits until the 10000th split...
	/// How often to split
	public final static int RANDOM_SPLIT_BASE = 10000;
	/// The frequency of random case splits (number per RANDOM_SPLIT_BASE elements)
	public final static int RANDOM_SPLIT_FREQ = 2;//TODO find a good value for this
	
	////// Quantifier Support
	/// The property for the pattern compiler
	public final static String PATTERNCOMPILER = 
		"de.uni_freiburg.informatik.ultimate.smtinterpol.convert.patterncompiler";
	/// The default pattern compiler
	public final static String DEFAULT_PATTERNCOMPILER = 
		"de.uni_freiburg.informatik.ultimate.smtinterpol.convert.DefaultPatternCompiler";
	/// Debug unused variable elimination
	public final static boolean DEBUG_QVAR_ELIMINATION = true;
	/// Don't infer looping patterns
	public final static boolean FEATURE_BLOCK_LOOPING_PATTERN = true;
	
	////// Proofs
	/// The name of the system property for proof processors
	public final static String PP_SYS_PROP_NAME = 
		"de.uni_freiburg.informatik.ultimate.smt.proof.processor";
	/// Check proofs for propositional validity
	public final static boolean CHECK_PROP_PROOF = !COMPETITION;
	
	////// Printing of results
	/// Include line breaks in output of lists
	public final static boolean RESULTS_ONE_PER_LINE = true;
	/// Indentation for nested s-exprs
	public static final int INDENTATION = 2;

	////// Usage Checks
	/// Stronger checks for usage (e.g., closed check in assertTerm)
	public final static boolean STRONG_USAGE_CHECKS = !COMPETITION;
	
	////// Optimizer
	/// Call optimizer for every formula
	public final static boolean OPTIMIZE_ALWAYS = false;
	/// Call optimizer after lifting of Term ITEs
	public final static boolean OPTIMIZE_LIFTED = false;

	////// Linear arithmetic configuration
	/// When to switch back to Bland's Rule (#vars * this_factor)
	public static final int BLAND_USE_FACTOR = 5;

	/**
	 * Should we do paranoid and expensive asserts.
	 */
	public static final boolean EXPENSIVE_ASSERTS = false;
}
