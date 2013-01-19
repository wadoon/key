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
package de.uni_freiburg.informatik.ultimate.logic;

/**
 * Representation of the response to a get-value command.
 * @author Juergen Christ
 */
public interface Valuation {
	/**
	 * Get the value for a term.  This function returns <code>null</code> if and
	 * only if the input term was not part of the get-value call. 
	 * @param t The term to get a value for.
	 * @return Value of the term or <code>null</code>.
	 */
	public Term get(Term t);
}
