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

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode.Antecedent;

public class OccurrenceCounter {
	/**
	 * The stack of clauses to be processed.
	 */
	private Deque<Clause> m_Todo = new ArrayDeque<Clause>();
	/**
	 * The count map.
	 */
	private Map<Clause, Integer> m_Counts;
	/**
	 * Increments the occurrence counter of a clause.  Returns <code>true</code>
	 * if this clause is seen for the first time.
	 * @param cls The clause.
	 * @return Is this clause seen for the first time in the proof tree.
	 */
	private boolean incCounter(Clause cls) {
		Integer oldVal = m_Counts.get(cls);
		int newVal = (oldVal != null) ? oldVal + 1 : 1;
		return m_Counts.put(cls, newVal) == null;
	}
	/**
	 * Compute for each clause in the proof tree the number of occurrences.
	 * Note that we do not compute deep occurrences, i.e., if a clause C2 occurs
	 * under a clause C1 which occurs multiple times, we do not increase the
	 * count of C2.
	 * @param unsat The proof tree.
	 * @return The occurrence map.
	 */
	public Map<Clause, Integer> count(Clause unsat) {
		assert unsat.getSize() == 0;
		m_Counts = new HashMap<Clause, Integer>();
		m_Todo.push(unsat);
		run();
		return m_Counts;
	}
	/**
	 * Process all clauses until the todo stack is empty.
	 */
	private void run() {
		while (!m_Todo.isEmpty()) {
			Clause cls = m_Todo.pop();
			if (incCounter(cls)) {
				// Descend into the subproof.
				ProofNode pn = cls.getProof();
				// Nothing to do for leaves.
				if (!pn.isLeaf()) {
					ResolutionNode rn = (ResolutionNode) pn;
					Antecedent[] antes = rn.getAntecedents();
					for (int i = antes.length - 1; i >= 0; --i)
						m_Todo.push((antes[i].antecedent));
					m_Todo.push(rn.getPrimary());
				}
			}
		}
	}
}
