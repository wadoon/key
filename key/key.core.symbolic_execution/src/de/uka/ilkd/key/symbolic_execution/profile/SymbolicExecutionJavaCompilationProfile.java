// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2016 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.profile;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.WhileInvariantRule;

/**
 * Nearly a clone of {@link SymbolicExecutionJavaProfile}, but with the loop
 * invariant rule disabled. There are special rules developed for compilation
 * that will treat loops instead.
 * 
 * @author Dominic Scheurer
 */
public class SymbolicExecutionJavaCompilationProfile extends
		SymbolicExecutionJavaProfile {
	/**
	 * The {@link Name} of this {@link Profile}.
	 */
	public static final String NAME = "Java Profile for Symbolic Execution for usage in compilation only";

	/**
	 * <p>
	 * The default instance of this class.
	 * </p>
	 * <p>
	 * It is typically used in the {@link Thread} of the user interface. Other
	 * instances of this class are typically only required to use them in
	 * different {@link Thread}s (not the UI {@link Thread}).
	 * </p>
	 */
	public static SymbolicExecutionJavaCompilationProfile defaultInstance;

	/**
	 * <p>
	 * The default instance of this class.
	 * </p>
	 * <p>
	 * It is typically used in the {@link Thread} of the user interface. Other
	 * instances of this class are typically only required to use them in
	 * different {@link Thread}s (not the UI {@link Thread}).
	 * </p>
	 */
	public static SymbolicExecutionJavaCompilationProfile defaultInstanceWithTruthValueEvaluation;

	/**
	 * Constructor.
	 * 
	 * @param predicateEvaluationEnabled
	 *            {@code true} predicate evaluation is enabled, {@code false}
	 *            predicate evaluation is disabled.
	 */
	public SymbolicExecutionJavaCompilationProfile(
			boolean predicateEvaluationEnabled) {
		super(predicateEvaluationEnabled);
	}

	/**
	 * <p>
	 * Returns the default instance of this class.
	 * </p>
	 * <p>
	 * It is typically used in the {@link Thread} of the user interface. Other
	 * instances of this class are typically only required to use them in
	 * different {@link Thread}s (not the UI {@link Thread}).
	 * </p>
	 * 
	 * @return The default instance for usage in the {@link Thread} of the user
	 *         interface.
	 */
	public static synchronized SymbolicExecutionJavaCompilationProfile getDefaultInstance() {
		return getDefaultInstance(false);
	}

	/**
	 * <p>
	 * Returns the default instance of this class.
	 * </p>
	 * <p>
	 * It is typically used in the {@link Thread} of the user interface. Other
	 * instances of this class are typically only required to use them in
	 * different {@link Thread}s (not the UI {@link Thread}).
	 * </p>
	 * 
	 * @param truthValueEvaluationEnabled
	 *            {@code true} truth value evaluation is enabled, {@code false}
	 *            truth value evaluation is disabled.
	 * @return The default instance for usage in the {@link Thread} of the user
	 *         interface.
	 */
	public static synchronized SymbolicExecutionJavaCompilationProfile getDefaultInstance(
			boolean truthValueEvaluationEnabled) {
		if (!truthValueEvaluationEnabled) {
			if (defaultInstance == null) {
				defaultInstance = new SymbolicExecutionJavaCompilationProfile(
						false);
			}
			return defaultInstance;
		} else {
			if (defaultInstanceWithTruthValueEvaluation == null) {
				defaultInstanceWithTruthValueEvaluation = new SymbolicExecutionJavaCompilationProfile(
						true);
			}
			return defaultInstanceWithTruthValueEvaluation;
		}
	}

	/**
	 * Same rules as in {@link SymbolicExecutionJavaProfile#initBuiltInRules()},
	 * but with the {@link WhileInvariantRule} removed.
	 */
	@Override
	protected ImmutableList<BuiltInRule> initBuiltInRules() {
		return super.initBuiltInRules()
				.removeFirst(WhileInvariantRule.INSTANCE);
	}
}
