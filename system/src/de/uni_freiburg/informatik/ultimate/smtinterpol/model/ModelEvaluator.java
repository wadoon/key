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
package de.uni_freiburg.informatik.ultimate.smtinterpol.model;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

/**
 * An evaluator for terms against the current model.
 * @author Juergen Christ
 */
public class ModelEvaluator extends TermTransformer {
	
	private final Model m_Model;

	public ModelEvaluator(Model model) {
		m_Model = model;
	}

	public Term evaluate(Term input) {
		return transform(input);
	}

	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] args) {
		setResult(m_Model.getValue(appTerm.getFunction(), args));
	}

	@Override
	protected void convert(Term term) {
		if (term instanceof QuantifiedFormula)
			throw new SMTLIBException(
					"Quantifier not allowed in model evaluation");
		super.convert(term);
	}
	
}
