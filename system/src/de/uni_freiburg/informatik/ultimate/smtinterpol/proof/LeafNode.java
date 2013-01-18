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

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;

/**
 * Proof node representing a leaf in the proof tree. This might either be an
 * input clause or a theory lemma.
 * @author Juergen Christ
 */
public class LeafNode extends ProofNode {
	/// No theory created this node => input clause.
	public final static byte NO_THEORY = 0;
	/// Quantifier Instantiation
	public final static byte QUANT_INST = 1;
	/// EUF-lemma
	public final static byte THEORY_CC = 2;
	/// LA(R/Z)-lemma
	public final static byte THEORY_LA = 3;
	/// NO equality propagation
	public final static byte EQ = 4;

	// TODO: WeakReference or SoftReference?
	private final byte m_theory;
	private IAnnotation m_annotation;
	
	public LeafNode(byte theory, IAnnotation annot) {
		m_theory = theory;
		m_annotation = annot;
	}
	
	@Override
	public boolean isLeaf() {
		return true;
	}
	/**
	 * Which theory created this leaf node.
	 * @return Identifier for the theory which created this leaf.
	 */
	public byte getTheory() {
		return m_theory;
	}
	/**
	 * Get theory specific annotations.
	 * @return Theory specific annotations.
	 */
	public IAnnotation getTheoryAnnotation() {
		return m_annotation;
	}
	/**
	 * Set theory specific annotations.
	 * @param annot New theory specific annotations.
	 */
	public void setTheoryAnnotation(IAnnotation annot) {
		m_annotation = annot;
	}
	public String toString() {
		return "[" + m_annotation + "]";
	}
}
