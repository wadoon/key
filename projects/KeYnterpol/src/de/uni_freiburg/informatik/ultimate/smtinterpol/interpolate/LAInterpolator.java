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
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffinTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.Occurrence;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.BoundConstraint;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitNumber;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAReason;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinVar;

public class LAInterpolator {

	Interpolator m_Interpolator;
	LAAnnotation m_Annotation;

	HashMap<LAAnnotation, LAReason> subAnnotToReason;
	
	HashMap<LAAnnotation, AnnotInfo> m_AuxInfos 
	= new HashMap<LAAnnotation, AnnotInfo>();

	class AnnotInfo extends Interpolator.Occurrence {
		LAAnnotation m_myAnnotation;
		
		private MutableAffinTerm m_Sum;		
		Interpolant[] m_Interpolants;

		InterpolatorAffineTerm m_mixedSums[];
		TermVariable m_AuxVar;
		InfinitNumber m_Epsilon;
		
		public AnnotInfo(LAAnnotation auxAnnot) {
			m_myAnnotation = auxAnnot;
			//we only need sum and stuff for subannotations
			if(!auxAnnot.equals(m_Annotation)) { 
				computeSum();
				color();
				computeMixedSums();
			}
		}
		
		void computeSum() {
			LAReason reason = subAnnotToReason.get(m_myAnnotation);
			m_Sum = new MutableAffinTerm();
			m_Sum.add(reason.isUpper() ? Rational.ONE : Rational.MONE, reason.getVar());
			m_Sum.add(reason.isUpper() ? reason.getBound().negate() : reason.getBound());
			m_Epsilon = reason.getVar().getEpsilon();
		}
		private void color() {
			int first = 0, last = m_Interpolator.m_NumInterpolants + 1;
			for (SharedTerm s : m_Sum.getSummands().keySet()) {
				Interpolator.Occurrence occ = 
						m_Interpolator.m_SymbolPartition.get(s);
				assert (occ != null);
				first = Math.max(first, occ.getFirstColor());
				last = Math.min(last, occ.getLastColor());
			}
			m_FirstColor = first;
			m_LastColor = last;
		}

		private void computeMixedSums() {
			if (m_FirstColor <= m_LastColor)
				return;
			m_mixedSums = new InterpolatorAffineTerm[m_FirstColor - m_LastColor];
			m_AuxVar = 
				m_Interpolator.m_Theory.createFreshTermVariable("msaux", 
						m_Sum.getSort(m_Interpolator.m_Theory));

			for (int part = m_LastColor; part < m_FirstColor; part++) {
				InterpolatorAffineTerm sumApart = new InterpolatorAffineTerm();

				LAReason reason = subAnnotToReason.get(m_myAnnotation);
				LinVar lv = reason.getVar();

				for(Entry<LinVar, BigInteger> en : lv.getLinTerm().entrySet()) {
					Occurrence occ = 
							m_Interpolator.m_SymbolPartition.get(
									en.getKey().getFlatTerm());

					if (occ.isALocal(part)) {
						Rational coeff = 
								Rational.valueOf(en.getValue(), BigInteger.ONE);
						sumApart.add(coeff, en.getKey());
					}
				}
				sumApart.add(Rational.MONE, m_AuxVar); 
				
				if (!reason.isUpper())
					sumApart.negate();

				m_mixedSums[part - m_LastColor] = sumApart;
			}
		}
		
		/**
		 * @return
		 */
		private MutableAffinTerm getSum() {
			return m_Sum;
			
		}
		
		InterpolatorAffineTerm getMixedSum(int part) {
			return m_mixedSums[part - m_LastColor];
		}

		public InfinitNumber getEpsilon() {
			return m_Epsilon;
		}
	}

	public LAInterpolator(Interpolator interpolator,
			LAAnnotation theoryAnnotation) {
		m_Interpolator = interpolator;
		m_Annotation = theoryAnnotation;
		
		subAnnotToReason = new HashMap<LAAnnotation, LAReason>();
		for (Entry<LAReason, LAAnnotation> en : 
			m_Annotation.getSubReasons().entrySet()) 
			subAnnotToReason.put(en.getValue(), en.getKey());
		
	}

	private AnnotInfo computeAuxAnnotations(LAAnnotation auxAnnot) {
		AnnotInfo result = m_AuxInfos.get(auxAnnot);
		if (result != null)
			return result;
		
		result = new AnnotInfo(auxAnnot);
		result.m_Interpolants = new Interpolant[m_Interpolator.m_NumInterpolants];
		for (int i = 0; i < m_Interpolator.m_NumInterpolants; i++)
			result.m_Interpolants[i] = new Interpolant();
 
		computeSubAnnotations(auxAnnot, result);

		interpolateLeafs(auxAnnot, result);

		interpolateInnerNodes(auxAnnot, result);

		m_AuxInfos.put(auxAnnot, result);		
		return result;
	}


	private void computeSubAnnotations(LAAnnotation auxAnnot, AnnotInfo result) {
		for (Entry<LAAnnotation, Rational> auxAnn : auxAnnot.getAuxAnnotations().entrySet()) {
			LAAnnotation annot = auxAnn.getKey();
			computeAuxAnnotations(annot); 
		}
	}

	/**
	 * Compute summaries and their restrictions if they are mixed, 
	 * then add it all up to an interpolant of the current auxAnnot 
	 */
	private void interpolateLeafs(LAAnnotation auxAnnot, AnnotInfo result) {
		InterpolatorAffineTerm[] ipl = new InterpolatorAffineTerm[m_Interpolator.m_NumInterpolants+1];
		for (int part = 0; part < ipl.length; part++)
			ipl[part] = new InterpolatorAffineTerm();
		@SuppressWarnings("unchecked")
		ArrayList<TermVariable>[] auxVars = 
			new ArrayList[m_Interpolator.m_NumInterpolants];
		Literal equality = null;
		LitInfo equalityInfo = null;
		Interpolator.Occurrence inequalityInfo = null;
		//if in a Subannotation add up the mixedSummaries to the interpolant, update the maps
		if(!auxAnnot.equals(m_Annotation)) {
			// Sum A parts of auxAnnot.
			int part = result.getLastColor();
			while (part < result.getFirstColor()) {
				
				ipl[part].add(Rational.MONE, result.getMixedSum(part));
				if (auxVars[part] == null)
					auxVars[part] = new ArrayList<TermVariable>();
				auxVars[part].add(result.m_AuxVar);
				part++;
			}
			while (part < ipl.length) {
				ipl[part].add(Rational.MONE, result.getSum());
				ipl[part].add(result.getEpsilon());
				part++;
			}
		}
		for (Entry<LAAnnotation, Rational> entry : auxAnnot.getAuxAnnotations().entrySet()) {
			AnnotInfo info = m_AuxInfos.get(entry.getKey());
			Rational coeff = entry.getValue();
			// Sum A parts of info.
			int part = info.getLastColor();
			while (part < info.getFirstColor()) {
				ipl[part].add(coeff, info.getMixedSum(part));
				if (auxVars[part] == null)
					auxVars[part] = new ArrayList<TermVariable>();
				auxVars[part].add(info.m_AuxVar);
				part++;
			}
			while (part < ipl.length) {
				ipl[part].add(coeff, info.getSum());
				part++;
			}
			inequalityInfo = info;
		}
		
		//interpolate leafs (?)
		for (Entry<Literal, Rational> entry : auxAnnot.getCoefficients().entrySet()) {
			
			Literal lit = entry.getKey().negate();
			Rational factor = entry.getValue();
			if (lit.getAtom() instanceof BoundConstraint || lit instanceof LAEquality) {
				InfinitNumber bound;
				LinVar lv;
				if (lit.getAtom() instanceof BoundConstraint) {
					BoundConstraint bc = (BoundConstraint) lit.getAtom();
					bound =	lit.getSign() > 0 ? bc.getBound() : bc.getInverseBound();
					lv = bc.getVar();
				} else  {
					assert lit instanceof LAEquality;
					LAEquality eq = (LAEquality) lit;
					lv = eq.getVar();
					bound = new InfinitNumber(eq.getBound(), 0);
				}
				LitInfo info = m_Interpolator.getLiteralInfo(lit.getAtom());
				inequalityInfo = info;

				int part = info.getLastColor();

				while (part < info.getFirstColor()) {
					/* ab-mixed interpolation */
					assert (info.m_MixedVar != null);
					ipl[part].add(factor, info.getAPart(part));
					ipl[part].add(factor.negate(), info.m_MixedVar);

					if (auxVars[part] == null)
						auxVars[part] = new ArrayList<TermVariable>();
					auxVars[part].add(info.m_MixedVar);
					part++;
				}
				while (part < ipl.length) {
					/* Literal in A: add to sum */
					ipl[part].add(factor, lv);
					ipl[part].add(bound.negate().mul(factor));
					part++;
				}
			} else if (lit.negate() instanceof LAEquality) {//we have a Nelson-Oppen Clause
				equality = lit.negate();
				LAEquality eq = (LAEquality) equality;
				//a NO-Clause (the equality) should have exactly one subannotation
				assert auxAnnot.getAuxAnnotations().size() + auxAnnot.getCoefficients().size()
				    + (auxAnnot == m_Annotation ? 0 : 1) == 3;
				assert equalityInfo == null;
				equalityInfo = m_Interpolator.getLiteralInfo(eq);
				assert factor.abs() == Rational.ONE;

				int part = equalityInfo.getLastColor();
				if (part < equalityInfo.getFirstColor()) {
					part = equalityInfo.getFirstColor();
				}
				while (part < ipl.length) {
					/* Literal in A: add epsilon to sum */
					ipl[part].add(eq.getVar().getEpsilon());
					part++;
				}
			}
		}
		assert (ipl[ipl.length-1].isConstant() 
				&& InfinitNumber.ZERO.less(ipl[ipl.length-1].getConstant()));
		
		/*
		 * save the interpolants computed for this leaf into result
		 * -- simply putting each into a leq0-atom does not suffice for the mixed ones, though
		 * there we have to put them into an EQInfo
		 */
		for (int part = 0; part < auxVars.length; part++) {
			Rational normFactor = ipl[part].isConstant() ? Rational.ONE
					: ipl[part].getGCD().inverse().abs();
			ipl[part].mul(normFactor);
			if (auxVars[part] != null) {
				TermVariable placeHolder = 
						m_Interpolator.m_Theory.createFreshTermVariable(
								"EQ", m_Interpolator.m_Theory.getBooleanSort());
				InfinitNumber k = ipl[ipl.length-1].getConstant().mul(normFactor).negate();
				if (ipl[part].isInt())
					k = k.floor();
				Term F = m_Interpolator.m_Theory.FALSE;
				if (equalityInfo != null 
					&& equalityInfo.isMixed(part)) {
					assert auxVars[part].size() == 2;
					assert normFactor == Rational.ONE;
					k = InfinitNumber.ZERO;
					F = m_Interpolator.m_Theory.and(
							ipl[part].toLeq0(m_Interpolator.m_Theory),
							m_Interpolator.m_Theory.equals
							(equalityInfo.getMixedVar(), 
							 auxVars[part].iterator().next()));
				}
				EQInfo eqIn = new EQInfo(ipl[part], k, F);
				for (TermVariable aux : auxVars[part])
					result.m_Interpolants[part].addMixedVarToEQ(aux, eqIn);
				result.m_Interpolants[part].m_term = placeHolder;
				result.m_Interpolants[part].m_EQToVar.put(eqIn, placeHolder);
			} else {
				assert (equalityInfo == null 
						|| !equalityInfo.isMixed(part));
				if (equalityInfo != null && ipl[part].isConstant()
					&& equalityInfo.isALocal(part) != inequalityInfo.isALocal(part)) {
					/* special case: Nelson-Oppen conflict, a < b and b<a in
					 * one partition, a!=b in the other.
					 * If a != b is in A, the interpolant is simply a!=b
					 * If a != b is in B, the interpolant is simply a==b
					 */
					Literal thisIpl = equalityInfo.isALocal(part) 
						? equality.negate() : equality;
					result.m_Interpolants[part].m_term = 
						thisIpl.getSMTFormula(m_Interpolator.m_Theory);
				} else {
					ipl[part].add(ipl[ipl.length-1].getConstant()
							.sub(InfinitNumber.EPSILON).mul(normFactor).negate());
					result.m_Interpolants[part].m_term = 
						ipl[part].toLeq0(m_Interpolator.m_Theory);
				}
			}
		}
	}

	
	private void interpolateInnerNodes(LAAnnotation auxAnnot, AnnotInfo result) {
		//interpolation of "inner nodes"
		for (Entry<LAAnnotation, Rational> auxAnn : auxAnnot.getAuxAnnotations().entrySet()) {
			LAAnnotation annot = auxAnn.getKey();
			AnnotInfo subInfo = computeAuxAnnotations(annot); 
			int part = 0;
			while (part < subInfo.getLastColor() && part < subInfo.getFirstColor()) {
				/* Literal in B: and */
				result.m_Interpolants[part].m_term = m_Interpolator.m_Theory.
						and(result.m_Interpolants[part].m_term, subInfo.m_Interpolants[part].m_term);
				m_Interpolator.mergeEQHashMaps(result.m_Interpolants[part], subInfo.m_Interpolants[part]);
				part++;
			}
			while (part < subInfo.getFirstColor()) {
				TermVariable mixedVar = subInfo.m_AuxVar;
				result.m_Interpolants[part] = m_Interpolator.mixedPivotLA(
						result.m_Interpolants[part], subInfo.m_Interpolants[part], mixedVar);
				part++;
			}
			while (part < subInfo.getLastColor()) {
				/* Literal is shared: ite */
				result.m_Interpolants[part].m_term = 
						m_Interpolator.m_Theory.ifthenelse
								(subInfo.getSum().toLeq0(m_Interpolator.m_Theory), 
								result.m_Interpolants[part].m_term, 
								subInfo.m_Interpolants[part].m_term);
				m_Interpolator.mergeEQHashMaps(result.m_Interpolants[part], subInfo.m_Interpolants[part]);
				part++;
			}
			while (part < m_Interpolator.m_NumInterpolants) {
				/* Literal in A: or */
				result.m_Interpolants[part].m_term = m_Interpolator.m_Theory.
						or(result.m_Interpolants[part].m_term, subInfo.m_Interpolants[part].m_term);
				m_Interpolator.mergeEQHashMaps(result.m_Interpolants[part], subInfo.m_Interpolants[part]);
				part++;
			}
		}
	}
	
	public Interpolant[] computeInterpolants() {
		AnnotInfo annotInfo = computeAuxAnnotations(m_Annotation);
		return annotInfo.m_Interpolants;
	}
}
