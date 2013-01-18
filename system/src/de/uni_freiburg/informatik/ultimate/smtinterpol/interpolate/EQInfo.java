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

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitNumber;

public class EQInfo {
	public EQInfo(InterpolatorAffineTerm t, InfinitNumber k, Term F) {
		m_t = t;
		m_k = k;
		m_F = F;
	}
	
	InterpolatorAffineTerm m_t;
	InfinitNumber m_k;
	Term m_F;
	
	public String toString() {
		return "EQ(" + m_t + ", " + m_k + ", " + m_F.toStringDirect() + ")";
	}
}
