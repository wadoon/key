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

import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;

/**
 * Class used as a response to get-assignments.  This class carries truth values
 * for all named Boolean terms that are asserted so far.
 * @author Juergen Christ
 */
public class Assignments {
	/**
	 * Iterator over all assignments with one specific Boolean value.  This is
	 * essentially a filtering iterator.
	 * @author Juergen Christ
	 */
	private class TruthIterator implements Iterator<String> {
		/**
		 * The value we want to filter.
		 */
		private Boolean m_TruthVal;
		/**
		 * The filtered iterator.
		 */
		private Iterator<Map.Entry<String, Boolean>> m_It;
		/**
		 * The next value to return.
		 */
		private String m_NextVal;
		/**
		 * Initialize the filter iterator.
		 * @param truthVal
		 */
		public TruthIterator(Boolean truthVal) {
			m_TruthVal = truthVal;
			m_It = Assignments.this.m_Assignment.entrySet().iterator();
			nextVal();
		}
		/**
		 * Search for the next value to return.
		 */
		private void nextVal() {			
			while (m_It.hasNext()) {
				Map.Entry<String, Boolean> me = m_It.next();
				if (me.getValue() == m_TruthVal) {
					m_NextVal = me.getKey();
					return;
				}
			}
			m_NextVal = null;
		}
		
		@Override
		public boolean hasNext() {
			return m_NextVal != null;
		}

		@Override
		public String next() {
			String val = m_NextVal;
			if (val == null)
				throw new NoSuchElementException();
			nextVal();
			return val;
		}

		@Override
		public void remove() {
			throw new UnsupportedOperationException();
		}
		
	}
	/**
	 * Store the assignment.
	 */
	private Map<String, Boolean> m_Assignment;
	/**
	 * The number of labels assigned to true.  This is lazily computed.
	 */
	private int m_NumTrue = -1;
	/**
	 * Construct a new assignment.
	 * @param assignment Map containing the assignments extracted by the solver.
	 */
	public Assignments(Map<String, Boolean> assignment) {
		m_Assignment = assignment;
	}
	/**
	 * Get the assignment of a named Boolean term.
	 * @param label Label of the Boolean term.
	 * @return Truth value assigned to the corresponding named Boolean term.
	 */
	public Boolean getAssignment(String label) {
		return m_Assignment.get(label);
	}
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append('(');
		for (Map.Entry<String, Boolean> me : m_Assignment.entrySet()) {
			sb.append('(').append(me.getKey()).append(' ').
				append(me.getValue()).append(')');
		}
		sb.append(')');
		return sb.toString();
	}
	/**
	 * Iterate over all labels whose corresponding named Boolean term is
	 * assigned <code>true</code> in the current model.
	 * @return Iterator over all satisfied named Boolean terms.
	 */
	public Iterable<String> getTrueAssignments() {
		return new Iterable<String>() {
			
			@Override
			public Iterator<String> iterator() {
				return new TruthIterator(Boolean.TRUE);
			}
		};
	}
	/**
	 * Iterate over all labels whose corresponding named Boolean term is
	 * assigned <code>false</code> in the current model.
	 * @return Iterator over all falsified named Boolean terms.
	 */
	public Iterable<String> getFalseAssignments() {
		return new Iterable<String>() {
			
			@Override
			public Iterator<String> iterator() {
				return new TruthIterator(Boolean.FALSE);
			}
		};
	}
	/**
	 * Get the number of labels assigned to true.
	 * @return Number of labels assigned to true.
	 */
	public int getNumTrueAssignments() {
		if (m_NumTrue == -1) {
			m_NumTrue = 0;
			for (Map.Entry<String, Boolean> me : m_Assignment.entrySet()) {
				if (me.getValue() == Boolean.TRUE)
					++m_NumTrue;
			}
		}
		return m_NumTrue;
	}
	/**
	 * Get the number of labels assigned to false.
	 * @return Number of labels assigned to false.
	 */
	public int getNumFalseAssignments() {
		return m_Assignment.size() - getNumTrueAssignments();
	}
}
