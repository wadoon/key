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

import java.util.ArrayDeque;
//import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class AnnotatedTerm extends Term {
	Term m_Subterm;
	private Annotation[] m_Annotations;
	
	AnnotatedTerm(Annotation[] annots, Term term, int hash) {
		super(hash);
		this.m_Annotations = annots;
		m_Subterm = term;
	}
	
	@Override
	public Sort getSort() {
		return m_Subterm.getSort();
	}
	
	public Term getSubterm() {
		return m_Subterm;
	}

	public Annotation[] getAnnotations() {
		return m_Annotations;
	}
	
	public static int hashAnnotations(Annotation[] annots, Term subTerm) {
		return //subTerm.hashCode() * 31 + Arrays.hashCode(annots);
			HashUtils.hashJenkins(subTerm.hashCode(), (Object[])annots);
	}
	
	@Override
	public void toStringHelper(ArrayDeque<Object> m_Todo) {
		// Add annotations to stack.
		m_Todo.addLast(")");
		Annotation[] annots = getAnnotations();
		for (int i = annots.length-1; i >= 0; i--) {
			m_Todo.addLast(annots[i].getValue());
			m_Todo.addLast(" "+annots[i].getKey()+" ");
		}
		m_Todo.addLast(getSubterm());
		m_Todo.addLast("(! ");
	}
}
