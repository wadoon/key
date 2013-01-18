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
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;

/**
 * Class used to annotate the input formulas such that interpolation is able to
 * discover the origin of a clause.
 * @author Juergen Christ
 */
public class SourceAnnotation implements IAnnotation {
	private final String m_annot;
	private final Term m_Source;
	public SourceAnnotation(String annot, Term source) {
		m_annot = annot;
		m_Source = source;
	}
	public String getAnnotation() {
		return m_annot;
	}
	public Term getSource() {
		return m_Source;
	}
	public String toString() {
		return m_annot;
	}
	@Override
	public String toSExpr(Theory smtTheory) {
		return m_annot.isEmpty() ? ":asserted" : ":asserted " + new QuotedObject(m_annot);
	}
}
