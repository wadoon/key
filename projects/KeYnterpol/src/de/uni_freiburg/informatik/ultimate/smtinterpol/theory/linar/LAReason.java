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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * Reason for a specific bound on a variable. 
 * 
 * The reason can be a literal that was set by the dpll engine 
 * ({@link LiteralReason}) or it is a composite reason ({@link CompositeReason})
 * build from the sum of other reasons.
 * Each LinVar keeps a list of reasons for upper and lower bounds, starting
 * with the most tight reason.
 * 
 * A special case are LiteralReasons that have inequalities as literals.  
 * These must have a strict bound and are followed by another reason 
 * explaining, why the bound holds non-strictly.  In integer arithmetic the
 * bound is an integer and the next bound is the next integer.
 * 
 * @see LiteralReason
 * @see CompositeReason
 * @author Juergen Christ, Jochen Hoenicke
 */
public abstract class LAReason {
	
	private LinVar m_var;
	protected InfinitNumber m_bound;
	int m_stackdepth;
	private LAReason m_oldReason;
	private boolean m_isUpper;
	/**
	 * The most recently asserted literal reason that caused this LAreason
	 * to be created.  If this class is a LiteralReason and was created
	 * by an asserted Literal this points to this class. 
	 */
	private LiteralReason m_lastlit;
	
	public LAReason(LinVar var, InfinitNumber bound, int depth, boolean isUpper,
			        LiteralReason lastLit) {
		m_var = var;
		m_bound = bound;
		m_stackdepth = depth;
		m_isUpper = isUpper;
		m_lastlit = lastLit == null ? (LiteralReason) this : lastLit;
	}
	/**
	 * Get the effective bound of this reason.
	 * @return Effective bound of this reason.
	 */
	public InfinitNumber getBound() {
		return m_bound;
	}
	
	/**
	 * Get the exact bound of this reason.
	 * @return Exact bound of this reason.
	 */
	public InfinitNumber getExactBound() {
		return m_bound;
	}
	
	public LinVar getVar() {
		return m_var;
	}
	
	public boolean isUpper() {
		return m_isUpper;
	}

	public int getStackDepth() {
		return m_stackdepth;
	}

	public LAReason getOldReason() {
		return m_oldReason;
	}

	public void setOldReason(LAReason old) {
		m_oldReason = old;
	}

	/**
	 * This returns the LiteralReason containing the most recent literal
	 * that was set and which contributed to this reason.
	 * This is the one that also stores this reason in its dependent list.
	 * @return the literal reason.
	 */
	public LiteralReason getLastLiteral() {
		return m_lastlit;
	}
	
	/**
	 * Explain this reason.  This may also explain a similar weaker formula
	 * weakened by a value less than slack and returns the slack minus the
	 * amount the formula was weakened.  The explanation of a upper bound  
	 * poly(x,y,z) <= bound is a set of literals  p_1(x,y,z) <= b_1,...,
	 * p_n(x,y,z) <= bn, with coefficient c_1,...,c_n >= 0, such that 
	 *  sum c_i p_i(x,y,z) = p(x,y,z)   and   sum c_i b_i = bound - eps, where
	 * eps < slack.  The return value of the function is slack - eps.
	 * The explanation is added to the annotation which contains a map that 
	 * assigns each literal p_i(x,y,z) <= b_i the coefficient c_i.
	 * @param slack a positive amount by which the formula may be weakened.
	 * @param literals the set of literals.
	 * @return the new positive slack that may be reduced. 
	 */
	abstract InfinitNumber explain(LAAnnotation annot, 
		InfinitNumber slack, Rational factor, LinArSolve solver);

	public String toString() {
		return m_var + (m_isUpper ? "<=" : ">=") + m_bound;
	}
}
