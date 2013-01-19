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
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class Interpolant {
	Term m_term;
	// HashMap<TermVariable, EQInfo> m_varToEQ = new HashMap<TermVariable,
	// EQInfo>();
	HashMap<EQInfo, TermVariable> m_EQToVar = new HashMap<EQInfo, TermVariable>();
	HashMap<TermVariable, HashSet<EQInfo>> m_mixedVarToEQs = new HashMap<TermVariable, HashSet<EQInfo>>();// ??

	public Interpolant() {
	}

	public Interpolant(Term term) {
		m_term = term;
	}

	public String toString() {
		if (m_EQToVar.isEmpty())
			return String.valueOf(m_term);
		else
			return m_term.toStringDirect() + m_EQToVar.toString();
	}

	public void addMixedVarToEQ(TermVariable auxVar, EQInfo eqInfo) {
		HashSet<EQInfo> hs = m_mixedVarToEQs.get(auxVar);
		if (hs == null) {
			hs = new HashSet<EQInfo>();
			m_mixedVarToEQs.put(auxVar, hs);
		}
		hs.add(eqInfo);
	}
}
