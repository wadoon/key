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

/**
 * This class does a recursive algorithm by using an explicit stack on 
 * the heap. 
 * 
 * If you need a stateless walker, you can just implement Walker.  If
 * your goal is to walk terms, then TermWalker may help you, as it already
 * dispatches the walk function based on the type of the term. A simple
 * term walker can be created as:
 * 
 * <pre>
 * class MyWalker extends TermWalker {
 *    MyWalker(Term term) { super(term) }
 *    walk(NonRecursiveWalker walker, final ApplicationTerm appTerm) {
 *       walker.addWorkItem(new NonRecursive.Walker() {
 *          public void walk(NonRecursiveWalker walker) {
 *             // ... code that should run after parameters are processed
 *          }
 *       }
 *       for (Term param : appTerm.getParameters()) {
 *          walker.enqueueWalker(new MyWalker(param));
 *       }
 *    }
 *    walk(... // handle other term classes...
 * </pre>
 * 
 * For stateful walker you need to extend the class NonRecursive.  In
 * addition you still need a Walker class that does the job.  It can
 * access the state by casting NonRecursive.
 * 
 * Results can be added in a stateful walker to an additional result
 * stack.  See FormulaUnLet as an example. 
 *
 * @see ComputeFreeVariables
 * @see FormulaUnLet
 * @author Jochen Hoenicke
 */
public class NonRecursive {
	/* This class iterates the term in a non-recursive way.  To achieve this
	 * it uses a todo stack, which contains terms and a small info how much
	 * of this term was already processed.  Additionally it uses a convert
	 * stack that contains the most recent converted terms, which is used 
	 * to collect the arguments of function calls and the subterm of other 
	 * terms.
	 */
	/**
	 * The todo stack. It contains the terms to convert and some info how much
	 * was already processed of this term.
	 */
	private ArrayDeque<Walker> m_Todo = new ArrayDeque<Walker>();
	
	protected interface Walker {
		/**
		 * Do one step of the recursive algorithm.  This may enqueue new
		 * walkers that do the remaining steps.
		 * @param engine The non recursive engine where new walkers 
		 * can be enqueued.
		 */
		public void walk(NonRecursive engine);
	}
	
	public void enqueueWalker(Walker item) {
		m_Todo.addLast(item);
	}
	
	/**
	 * The main work horse.  This will repeat doing work items until the
	 * todo stack is empty.
	 */
	public void run(Walker item) {
		m_Todo.addLast(item);
		run();
	}
	public void run() {
		while (!m_Todo.isEmpty()) {
			m_Todo.removeLast().walk(this);
		}
	}
	
	public String toString() {
		return m_Todo.toString();
	}
	
	public static abstract class TermWalker implements Walker {
		Term m_Term;
		public TermWalker(Term term) {
			m_Term = term;
		}
		public void walk(NonRecursive walker) {
			if (m_Term instanceof ApplicationTerm)
				walk(walker, (ApplicationTerm) m_Term);
			else if (m_Term instanceof LetTerm)
				walk(walker, (LetTerm) m_Term);
			else if (m_Term instanceof AnnotatedTerm)
				walk(walker, (AnnotatedTerm) m_Term);
			else if (m_Term instanceof QuantifiedFormula)
				walk(walker, (QuantifiedFormula) m_Term);
			else if (m_Term instanceof ConstantTerm)
				walk(walker, (ConstantTerm) m_Term);
			else if (m_Term instanceof TermVariable)
				walk(walker, (TermVariable) m_Term);
		}

		public abstract void walk(NonRecursive walker, ConstantTerm term);
		public abstract void walk(NonRecursive walker, AnnotatedTerm term);
		public abstract void walk(NonRecursive walker, ApplicationTerm term);
		public abstract void walk(NonRecursive walker, LetTerm term);
		public abstract void walk(NonRecursive walker, QuantifiedFormula term);
		public abstract void walk(NonRecursive walker, TermVariable term);
		
		public Term getTerm() {
			return m_Term;
		}

		public String toString() {
			return getClass().getSimpleName()+":"+m_Term;
		}
	}
}
