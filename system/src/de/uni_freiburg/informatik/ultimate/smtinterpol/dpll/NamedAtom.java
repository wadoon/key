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
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class NamedAtom extends DPLLAtom {
	final TermVariable name;
	final Term smtAtom;
	
	public NamedAtom(TermVariable name, Term smtAtom, int assertionstacklevel) {
		super(smtAtom.hashCode(), assertionstacklevel);
		this.name = name;
		this.smtAtom = smtAtom;
	}
	
	public String toString() {
		return name.toString();
	}

	public Term getSMTFormula(Theory smtTheory, boolean useAuxVars) {
		return useAuxVars ? name : smtAtom;
	}
	
	public int containsTerm(TermVariable tv) {
		return 0;
	}
	
	public boolean equals(Object other) {
		return other instanceof NamedAtom &&
			((NamedAtom) other).smtAtom == smtAtom;
	}
}
