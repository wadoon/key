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
package de.uni_freiburg.informatik.ultimate.smtinterpol.dpll;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;


public abstract class Literal {
	DPLLAtom atom;
	protected Literal  negated;
	Clause.WatchList watchers = new Clause.WatchList();

	private final int hash;
	@Override
	public final int hashCode() {
		return hash;
	}
	
	public Literal(int hash) {
		this.hash = hash;
	}
	
	/**
	 * Returns the underlying atom.  If this literal is an atom, it returns
	 * itself.
	 */
	public final DPLLAtom getAtom() { return atom; }
	/**
	 * Returns the negated literal.
	 */
	public final Literal  negate()  { return negated; }
	/**
	 * Returns the sign of the literal (1 for atom, -1 for negated atom).
	 */
	public abstract int getSign();
	/**
	 * Returns a SMT representation of the literal.
	 * @return a SMT representation of the literal.
	 */
	public abstract Term getSMTFormula(Theory smtTheory, boolean useAuxVars);
	/**
	 * Returns a SMT representation of the literal.
	 * @return a SMT representation of the literal.
	 */
	public final Term getSMTFormula(Theory smtTheory) {
		return getSMTFormula(smtTheory, false);
	}
}
