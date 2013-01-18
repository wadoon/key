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

import java.math.BigInteger;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * Class representing a linear term c1*x1+...+cn*xn
 * 
 * @author Juergen Christ
 */
public class LinTerm {
	// coefficient map has to be initialized before mvar!!!
	Map<LinVar,BigInteger> mcoeffs;
	/**
	 * Generate a new linear term. Note that we do not make a copy of the given
	 * map. 
	 * @param coeffmap Coefficient map to use.
	 */
	LinTerm(Map<LinVar,BigInteger> coeffmap) {
		mcoeffs = coeffmap;
	}
	public String toString() {
		if (mcoeffs.isEmpty())
			return "0";
		StringBuilder sb = new StringBuilder();
		boolean isFirst = true;
		for (Entry<LinVar,BigInteger> entry : mcoeffs.entrySet()) {
			LinVar var = entry.getKey();
			BigInteger fact = entry.getValue();
			if (fact.signum() == -1) {
				sb.append(isFirst ? "-" : " - ");
			} else {
				sb.append(isFirst ? "" : " + ");
			}
			fact = fact.abs();
			if (!fact.equals(Rational.ONE))
				sb.append(fact).append("*");
			sb.append(var);
			isFirst = false;
		}
		return sb.toString();
	}
	public int hashCode() {
		return mcoeffs.hashCode();
	}
	public boolean equals(Object o) {
		if( o instanceof LinTerm )
			return mcoeffs.equals(((LinTerm)o).mcoeffs);
		return false;
	}
}
