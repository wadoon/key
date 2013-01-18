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

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.ConvertFormula;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.FlatApplicationTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.FlatTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode.Antecedent;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.BoundConstraint;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitNumber;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinVar;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffinTerm;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;


public class Interpolator {

	static class Occurrence {
		int m_FirstColor;
		int m_LastColor;

		public Occurrence() {
			m_FirstColor = Integer.MAX_VALUE;
			m_LastColor = -1;
		}

		public Occurrence(int first, int last) {
			m_FirstColor = first;
			m_LastColor = last;
		}

		public void occursIn(int partition) {
			if (m_FirstColor > partition)
				m_FirstColor = partition;
			if (m_LastColor < partition)
				m_LastColor = partition;
		}

		public boolean contains(int partition) {
			return (m_FirstColor <= partition
					&& m_LastColor >= partition);
		}

		public int getFirstColor() {
			return m_FirstColor;
		}

		public int getLastColor() {
			return m_LastColor;
		}

		public boolean isAorShared(int partition) {
			return m_FirstColor <= partition;
		}
		public boolean isBorShared(int partition) {
			return m_LastColor > partition;
		}
		public boolean isALocal(int partition) {
			return m_FirstColor <= partition 
					&& m_LastColor <= partition;
		}
		public boolean isBLocal(int partition) {
			return m_FirstColor > partition 
					&& m_LastColor > partition;
		}
		public boolean isAB(int partition) {
			return m_FirstColor <= partition 
					&& m_LastColor > partition;
		}
		public boolean isMixed(int partition) {
			return m_FirstColor > partition 
					&& m_LastColor <= partition;
		}

		public String toString() {
			return "["+m_FirstColor+"-"+m_LastColor+"]";
		}
	}

	static class LitInfo extends Occurrence {
		TermVariable m_MixedVar;
		/** Tells for an equality whether the A part is the Lhs or
		 * the Rhs.
		 */
		boolean m_MixedAOnLeft;
		/** 
		 * Gives for an inequality the A part.
		 */
		MutableAffinTerm[] m_APart;

		public LitInfo() {
			super();
		}

		public LitInfo(int firstColor, int lastColor) {
			super(firstColor, lastColor);
		}

		public TermVariable getMixedVar() {
			return m_MixedVar;
		}

		public boolean isAOnLeft() {
			return m_MixedAOnLeft;
		}

		public MutableAffinTerm getAPart(int p) {
			return m_APart[p - m_LastColor];
		}
	}

	Logger m_Logger;
	Theory m_Theory;
	int m_NumInterpolants;
	HashMap<SharedTerm, Occurrence> m_SymbolPartition;
	HashMap<DPLLAtom, LitInfo> m_LiteralInfos;
	HashMap<String, Integer> m_Partitions;
	HashMap<Clause, Interpolant[]> m_Interpolants;
	ConvertFormula m_Converter;
	
	

	public Interpolator(Logger logger, Theory theory, 
			Set<String>[] partitions, ConvertFormula converter) {
		m_Partitions = new HashMap<String, Integer>();
		for (int i = 0; i < partitions.length; i++) {
			Integer part = i;
			for (String name: partitions[i]) {
				m_Partitions.put(name, part);
			}
		}
		m_Logger = logger;
		m_Theory = theory;
		m_Converter = converter;
		m_NumInterpolants = partitions.length - 1;

		m_SymbolPartition = new HashMap<SharedTerm, Occurrence>();
		m_LiteralInfos = new HashMap<DPLLAtom, LitInfo>();
		m_Interpolants = new HashMap<Clause,Interpolant[]>();
	}

	private Term unfoldEQs(Interpolant interpolant) {
		FormulaSubstitutor substitutor = new FormulaSubstitutor();
		for (Entry<EQInfo, TermVariable> en : interpolant.m_EQToVar.entrySet()) {
			EQInfo eqInfo = en.getKey();
			assert(eqInfo.m_t.m_constant.meps >= 0);
			assert(eqInfo.m_k.meps <= 0);
			InterpolatorAffineTerm tPlusK = 
					new InterpolatorAffineTerm(eqInfo.m_t);
			tPlusK.add(eqInfo.m_k);
			tPlusK.add(InfinitNumber.EPSILON);
			if (tPlusK.isInt())
				tPlusK.m_constant = tPlusK.m_constant.ceil();

			Term formula = 
					m_Theory.or(tPlusK.toLeq0(m_Theory), en.getKey().m_F);
			substitutor.addSubstitution(en.getValue(), formula);
		}
		return substitutor.transform(interpolant.m_term);
	}

	public Term[] getInterpolants(Clause refutation) {
		colorLiterals(refutation, new HashSet<Clause>());
		Interpolant[] eqitps = interpolate(refutation);
		Term[] itpTerms = new Term[eqitps.length];
		for (int i = 0; i < eqitps.length; i++) 
			itpTerms[i] = unfoldEQs(eqitps[i]);
//		for (int i = 0; i < eqitps.length; i++)
//			m_Logger.info(itpTerms[i].toStringDirect());
		return itpTerms;
	}

	public Interpolant[] interpolate(Clause cl) {
		if (m_Interpolants.containsKey(cl))
			return m_Interpolants.get(cl);

		Interpolant[] interpolants = null;
		ProofNode proof = cl.getProof();
		if (!proof.isLeaf()) {
			ResolutionNode resNode = (ResolutionNode) proof;
			Clause prim = resNode.getPrimary();
			Interpolant[] primInterpolants = interpolate(prim);
			interpolants = new Interpolant[m_NumInterpolants];
			for (int i = 0; i < m_NumInterpolants; i++) {
				interpolants[i] = new Interpolant(primInterpolants[i].m_term);
				addAllHashMapSets(interpolants[i].m_mixedVarToEQs, primInterpolants[i].m_mixedVarToEQs);
				interpolants[i].m_EQToVar = new HashMap<EQInfo,TermVariable>(primInterpolants[i].m_EQToVar);
			}
			
			m_Logger.debug(new DebugMessage("Resolution Primary: {0}", prim));

			for (Antecedent assump : resNode.getAntecedents()) {
				Interpolant[] assInterp = interpolate(assump.antecedent);
				Literal pivot = assump.pivot;
				LitInfo pivInfo = m_LiteralInfos.get(pivot.getAtom());

				m_Logger.debug(new DebugMessage("Interpolating for {0}", assump));

				for (int i = 0; i < m_NumInterpolants; i++) {
					m_Logger.debug(new DebugMessage
							("Pivot {2}{3} on interpolants {0} and {1} gives...", 
									interpolants[i], assInterp[i], 
									pivot.getSMTFormula(m_Theory), pivInfo));
					if (pivInfo.isALocal(i)) {
						interpolants[i].m_term = 
								m_Theory.or(interpolants[i].m_term, assInterp[i].m_term);
						mergeEQHashMaps(interpolants[i], assInterp[i]);
					} else if (pivInfo.isBLocal(i)) {
						interpolants[i].m_term = 
								m_Theory.and(interpolants[i].m_term, assInterp[i].m_term);
						mergeEQHashMaps(interpolants[i], assInterp[i]);
					} else if (pivInfo.isAB(i)) {
						interpolants[i].m_term = 
								m_Theory.ifthenelse(pivot.getSMTFormula(m_Theory), 
										interpolants[i].m_term, assInterp[i].m_term);
						mergeEQHashMaps(interpolants[i], assInterp[i]);
					} else {
						if (pivot.getAtom() instanceof CCEquality ||
								pivot.getAtom() instanceof LAEquality) {
							Interpolant eqIpol, neqIpol;
							if (pivot.getSign() > 0) {
								eqIpol = assInterp[i];
								neqIpol = interpolants[i];
							} else {
								eqIpol = interpolants[i];
								neqIpol = assInterp[i];
							}
							interpolants[i] = mixedEqInterpolate(
									eqIpol, neqIpol, pivInfo.m_MixedVar);
						} else if (pivot.getAtom() instanceof BoundConstraint) {
							interpolants[i] = mixedPivotLA(
									assInterp[i], interpolants[i], pivInfo.m_MixedVar);
						} else {
							throw new UnsupportedOperationException
							("Cannot handle mixed literal "+pivot);
						}
					}
					m_Logger.debug(interpolants[i]);
				}
			}
		} else {
			LeafNode leaf = (LeafNode) proof;
			if (leaf.getTheory() == LeafNode.NO_THEORY) {
				SourceAnnotation annot = 
						(SourceAnnotation) leaf.getTheoryAnnotation();
				int partition = m_Partitions.get(annot.getAnnotation());
				interpolants = new Interpolant[m_NumInterpolants];
				for (int i = 0; i < m_NumInterpolants; i++) {
					interpolants[i] = new Interpolant(partition <= i
							? m_Theory.FALSE : m_Theory.TRUE); 
				}
			} else if  (leaf.getTheory() == LeafNode.THEORY_CC) {
				CCInterpolator ipolator = new CCInterpolator(this);
				Term[] interpolantTerms = ipolator.computeInterpolants
						((CCAnnotation) leaf.getTheoryAnnotation());
				interpolants = new Interpolant[m_NumInterpolants];
				for (int j = 0; j < m_NumInterpolants; j++) { 
					interpolants[j] = new Interpolant(interpolantTerms[j]);
				}
			} else if  (leaf.getTheory() == LeafNode.THEORY_LA) {
				LAInterpolator ipolator =
						new LAInterpolator(this,
								(LAAnnotation) leaf.getTheoryAnnotation());
				interpolants = ipolator.computeInterpolants();
			} else if  (leaf.getTheory() == LeafNode.EQ) {
				assert cl.getSize() == 2;
				Literal l1 = cl.getLiteral(0);
				Literal l2 = cl.getLiteral(1);
				assert l1.getSign() != l2.getSign();
				if (l1.getAtom() instanceof LAEquality) {
					l1 = cl.getLiteral(1);
					l2 = cl.getLiteral(0);
				}
				interpolants = computeEQInterpolant
					((CCEquality) l1.getAtom(),	(LAEquality) l2.getAtom(),
					l1.getSign());
			} else {
				throw new UnsupportedOperationException("Cannot interpolate "+proof);
			}
		}

		m_Interpolants.put(cl, interpolants);
		return interpolants;
	}

	/**
	 * Compute the interpolant for a Nelson-Oppen equality clause. This is a
	 * theory lemma of the form equality implies equality, where one equality
	 * is congruence closure and one is linear arithmetic.
	 * @param ccEq  the congruence closure equality atom 
	 * @param laEq  the linear arithmetic equality atom
	 * @param sign the sign of l1 in the conflict clause. This is -1 if
	 * 	l1 implies l2, and +1 if l2 implies l1. 
	 */
	private Interpolant[] computeEQInterpolant(CCEquality ccEq, LAEquality laEq,
			int sign) {
		Interpolant[] interpolants = null;
		LitInfo ccInfo = getLiteralInfo(ccEq);
		LitInfo laInfo = getLiteralInfo(laEq);
		
		interpolants = new Interpolant[m_NumInterpolants];
		for (int p = 0; p < m_NumInterpolants; p++) {
			Term interpolant; 
			if (ccInfo.isAorShared(p) && laInfo.isAorShared(p))
				interpolant = m_Theory.FALSE; // both literals in A.
			else if (ccInfo.isBorShared(p) && laInfo.isBorShared(p))
				interpolant = m_Theory.TRUE; // both literals in B.
			else {
				InterpolatorAffineTerm iat = new InterpolatorAffineTerm();
				Rational factor = ccEq.getLAFactor();
				TermVariable mixed = null;
				boolean negate = false;
				// Get A part of ccEq:
				if (ccInfo.isALocal(p)) {
					iat.add(factor, ccEq.getLhs().getFlatTerm());
					iat.add(factor.negate(), ccEq.getRhs().getFlatTerm());
					if (sign == 1)
						negate = true;
				} else if (ccInfo.isMixed(p)) {
					// mixed;
					if (sign == 1)
						mixed = ccInfo.getMixedVar();
					if (ccInfo.m_MixedAOnLeft) {
						iat.add(factor, ccEq.getLhs().getFlatTerm());
						iat.add(factor.negate(), ccInfo.getMixedVar());
					} else {
						iat.add(factor, ccInfo.getMixedVar());
						iat.add(factor.negate(), ccEq.getRhs().getFlatTerm());
					}
				} else {
					// both sides in B, A part is empty
				}
				
				// Get A part of laEq:
				if (laInfo.isALocal(p)) {
					iat.add(Rational.MONE, laEq.getVar());
					iat.add(laEq.getBound());
					if (sign == -1)
						negate = true;
				} else if (laInfo.isMixed(p)) {
					if (sign == -1)
						mixed = laInfo.getMixedVar();
					iat.add(Rational.MONE, laInfo.getAPart(p));
					iat.add(Rational.ONE, laInfo.getMixedVar());
				} else {
					// both sides in B, A part is empty
				}
				iat.mul(iat.getGCD().inverse());
				
				// Now solve it.
				if (mixed != null) {
					Rational mixedFactor = iat.getSummands().remove(mixed);
					assert(mixedFactor.isIntegral());
					boolean isInt = mixed.getSort().getName().equals("Int");
					if (isInt && mixedFactor.abs() != Rational.ONE) {
						if (mixedFactor.signum() > 0)
							iat.negate();
						Term sharedTerm = iat.toSMTLib(m_Theory, isInt);
						interpolant =
							m_Theory.equals(mixed, 
								m_Theory.term("div", sharedTerm, m_Theory.numeral(mixedFactor.numerator())));
						FunctionSymbol divisible = m_Theory.getFunctionWithResult("divisible", 
								new BigInteger[] {mixedFactor.numerator()},
								null, m_Theory.getSort("Int"));
						interpolant = m_Theory.and(interpolant, m_Theory.term(divisible, sharedTerm));
					} else {
						iat.mul(mixedFactor.negate().inverse());
						Term sharedTerm = iat.toSMTLib(m_Theory, isInt);
						interpolant =
								m_Theory.equals(mixed, sharedTerm);
					}
				} else {
					if (iat.isConstant()) {
						if (iat.getConstant() != InfinitNumber.ZERO)
							negate = !negate;
						interpolant = negate ? m_Theory.FALSE : m_Theory.TRUE;
					} else {
						boolean isInt = iat.isInt();
						Term term = iat.toSMTLib(m_Theory, isInt);
						Term zero = iat.isInt()
							? m_Theory.numeral(BigInteger.ZERO)
							: m_Theory.decimal(BigDecimal.ZERO);
						interpolant = negate ? m_Theory.distinct(term, zero)
									: m_Theory.equals(term, zero);
					}
				}
			}
			interpolants[p] = new Interpolant(interpolant);
		}
		return interpolants;
	}

	private Interpolant mixedEqInterpolate(Interpolant eqIpol,
			final Interpolant neqIpol, final TermVariable mixedVar) {
		final Interpolant newI = new Interpolant();
		TermTransformer substitutor = new TermTransformer() {
			public void convert(Term term) {
				assert term != mixedVar;
				if (term instanceof ApplicationTerm) {
					ApplicationTerm appTerm = (ApplicationTerm) term;
					if (appTerm.getParameters().length == 2 && 
						(appTerm.getParameters()[0] == mixedVar
						 || appTerm.getParameters()[1] == mixedVar)) {
						assert appTerm.getFunction().isIntern()
							&& appTerm.getFunction().getName().equals("=")
							&& appTerm.getParameters().length == 2;
						
						Term s = appTerm.getParameters()[1];
						if (s == mixedVar)
							s = appTerm.getParameters()[0];
						setResult(m_Theory.let(mixedVar, s, neqIpol.m_term));
						return;
					}
				}
				if (term instanceof LetTerm) {
					LetTerm let = (LetTerm) term;
					for (TermVariable tv : let.getVariables()) {
						if (tv == mixedVar) {
							setResult(term);
							return;
						}
					}
				}
				super.convert(term);
			}
		};
		
		newI.m_EQToVar.putAll(eqIpol.m_EQToVar);
		addAllHashMapSets(newI.m_mixedVarToEQs, eqIpol.m_mixedVarToEQs);
		newI.m_EQToVar.putAll(neqIpol.m_EQToVar);
		addAllHashMapSets(newI.m_mixedVarToEQs, neqIpol.m_mixedVarToEQs);

		newI.m_term = substitutor.transform(eqIpol.m_term);
//		if (eqIpol.m_mixedVarToEQs.get(mixedVar) != null) {
			for (EQInfo eq : eqIpol.m_EQToVar.keySet()) { //eqIpol.m_mixedVarToEQs.get(mixedVar)) {
				EQInfo newEq = new EQInfo(eq.m_t, eq.m_k, substitutor.transform(eq.m_F));
				newI.m_EQToVar.put(newEq, newI.m_EQToVar.remove(eq));
				for (HashSet<EQInfo> eqs : newI.m_mixedVarToEQs.values()) {
					if (eqs.remove(eq))
						eqs.add(newEq);
				}
			}
//		}
		return newI;
	}
	
	/**
	 * Used for constructing I2(s) for mixedEQInterpolation (interpolation of equality literals).
	 * replace all occurrences of an auxiliary TermVar by a Term in an interpolant -- term and EQInfos
	 * new EQInfos are created if something inside an EQ is changed
	 * @param itpTerm term of the interpolant I2.
	 * @param auxVar  the auxiliary variable of the pivot literal.
	 * @param replacement the s in I2(s).
	 * @param mixedVarToEQs mapping from the interpolant I2.
	 * @param EQToVar mapping from the interpolant I2.
	 */
	Interpolant substituteInInterpolant(Term itpTerm, TermVariable auxVar, Term replacement,
			HashMap<TermVariable, HashSet<EQInfo>> mixedVarToEQs, HashMap<EQInfo, TermVariable> EQToVar) {
		Interpolant newItp = new Interpolant(substitute(itpTerm, replacement, auxVar));
		
		HashSet<EQInfo> concernedEQs = mixedVarToEQs.get(auxVar);
		
		if(concernedEQs == null) {
			return newItp;
		} else {
			//make copies of the EQs where something is to be changed
			HashMap<TermVariable, TermVariable> origToCopy = new HashMap<TermVariable, TermVariable>();
			for (EQInfo eqi : concernedEQs) {
				EQInfo copyEQ = new EQInfo(new InterpolatorAffineTerm(eqi.m_t), eqi.m_k, eqi.m_F);

				TermVariable origTV = EQToVar.get(eqi);
				TermVariable copyTV = m_Theory.createFreshTermVariable("EQ_cp", origTV.getSort());
				origToCopy.put(origTV, copyTV);

				newItp.m_EQToVar.put(copyEQ, copyTV);
//				newItp.m_varToEQ.put(copyTV, copyEQ);
				//TODO ?? this should only be the case when there are no auxVars in the Interpolant
				if (newItp.m_mixedVarToEQs.get(auxVar) != null) { 
					newItp.m_mixedVarToEQs.get(auxVar).add(copyEQ);
					newItp.m_mixedVarToEQs.get(auxVar).remove(eqi);				
				}
				newItp.m_EQToVar.remove(eqi);
//				newItp.m_varToEQ.remove(origTV);
			}

			//for every concerned EQ: replace it by its copy
			// TODO only substitute once both auxvar and EQvars, e.g. via FormulaUnLet.
			for (TermVariable tv : newItp.m_term.getFreeVars())
				if (origToCopy.get(tv) != null)
					newItp.m_term = substitute(newItp.m_term, origToCopy.get(tv), tv);
			//--> obsolete by recursion (right?) 
			//	--> no! this is about putting the copies in place of the originals

			//for every copy: 
			for (EQInfo eq : newItp.m_EQToVar.keySet()) {
				//substitute in the Formula
				eq.m_F = substitute(eq.m_F, replacement, auxVar);
				for (TermVariable tv : eq.m_F.getFreeVars()) //??
					if (origToCopy.get(tv) != null)
						eq.m_F = substitute(eq.m_F, origToCopy.get(tv), tv);
//						eq.m_F = substituteInInterpolant(//TODO recursive magic here -- correct??
//								eq.m_F, auxVar, replacement, mixedVarToEQs, EQToVar).m_term;

				//substitute in the MutableAffinTerm
				Rational coeff = eq.m_t.getSummands().remove(auxVar);
				eq.m_t.add(coeff, replacement);
			}
			return newItp;
		}
	}

	static <K,V>void addAllHashMapSets(HashMap<K, HashSet<V>> dest, HashMap<K, HashSet<V>> src) {
		for (Entry<K,HashSet<V>> entry: src.entrySet()) {
			HashSet<V> orig = dest.get(entry.getKey());
			if (orig != null)
				orig.addAll(entry.getValue());
			else
				dest.put(entry.getKey(), new HashSet<V>(entry.getValue()));
		}
	}
	
	/**
	 * the result of the merge is saved in ip1 (TODO vllt doch inlinen..)
	 * @param ip1
	 * @param ip2
	 */
	public void mergeEQHashMaps(Interpolant ip1, Interpolant ip2) {
		ip1.m_EQToVar.putAll(ip2.m_EQToVar);
		//		ip1.m_varToEQ.putAll(ip2.m_varToEQ);
		addAllHashMapSets(ip1.m_mixedVarToEQs, ip2.m_mixedVarToEQs);
	}

	/**
	 * Substitute termVar by replacement in mainTerm
	 * @param mainTerm
	 * @param replacement
	 * @param termVar
	 * @return substituted Term
	 */
	Term substitute(Term mainTerm, final Term replacement,
			final TermVariable termVar) {
		boolean termVarIsFree = false;
		for (TermVariable t : mainTerm.getFreeVars()) {
			if(t.equals(termVar))
				termVarIsFree = true;
		}
		if(!termVarIsFree)
			return mainTerm;

		return new TermTransformer() {
			public void convert(Term term) {
				if (term.equals(termVar))
					setResult(replacement);
				else
					super.convert(term);
			}
		}.transform(mainTerm);
	}

	public void colorLiterals(Clause root, HashSet<Clause> visited) {
		if (visited.contains(root))
			return;
		visited.add(root);
		ProofNode pn = root.getProof();
		if (pn.isLeaf()) {
			LeafNode ln = (LeafNode) pn;
			if (ln.getTheory() == LeafNode.NO_THEORY) {
				SourceAnnotation annot = 
						(SourceAnnotation) ln.getTheoryAnnotation();
				int partition = m_Partitions.get(annot.getAnnotation());
				for (int i = 0; i < root.getSize(); i++) {
					Literal lit = root.getLiteral(i);
					DPLLAtom atom = lit.getAtom();
					LitInfo info = m_LiteralInfos.get(atom);
					if (info == null) {
						info = new LitInfo();
						m_LiteralInfos.put(atom, info);
					}
					if (!info.contains(partition)) {
						info.occursIn(partition);
						if (atom instanceof CCEquality) {
							CCEquality eq = (CCEquality)atom;
							addOccurrence(eq.getLhs().getFlatTerm(), partition);
							addOccurrence(eq.getRhs().getFlatTerm(), partition);
						} else if (atom instanceof BoundConstraint) {
							LinVar lv = ((BoundConstraint) atom).getVar();
							addOccurrence(lv, partition);
						} else if (atom instanceof LAEquality) {
							LinVar lv = ((LAEquality) atom).getVar();
							addOccurrence(lv, partition);
						}
					}
				}
			}
		} else {
			ResolutionNode rn = (ResolutionNode) pn;
			colorLiterals(rn.getPrimary(), visited);
			for (Antecedent a : rn.getAntecedents()) {
				colorLiterals(a.antecedent, visited);
			}
		}
	}


	Occurrence getOccurrence(SharedTerm shared) {
		Occurrence result = m_SymbolPartition.get(shared);
		if (result == null) {
			result = new Occurrence();
			if (shared instanceof FlatApplicationTerm) {
				FlatApplicationTerm flatAppTerm = (FlatApplicationTerm) shared;
				SourceAnnotation annot = flatAppTerm.getSourceAnnotation();
				if (annot !=  null) {
					int partition = m_Partitions.get(annot.getAnnotation());
					result.occursIn(partition);
				}
			}
			m_SymbolPartition.put(shared, result);
		}
		return result;
	}

	void addOccurrence(SharedTerm term, int part) {
		getOccurrence(term).occursIn(part);
		if (term instanceof SharedAffineTerm
			&& term.getLinVar() != null) {
			addOccurrence(term.getLinVar(), part);
		} else if (term instanceof FlatApplicationTerm) {
			for (FlatTerm param : ((FlatApplicationTerm)term).getParameters()){
				addOccurrence(param.toShared(), part);
			}
		}
	}

	void addOccurrence(LinVar var, int part) {
		if (var.isInitiallyBasic()) {
			for (LinVar c : var.getLinTerm().keySet())
				addOccurrence(c.getFlatTerm(), part);
		} else {
			addOccurrence(var.getFlatTerm(), part);
		}
	}

	LitInfo getLiteralInfo(DPLLAtom lit) {
		LitInfo result = m_LiteralInfos.get(lit);
		if (result == null)
			result = colorMixedLiteral(lit);
		return result;
	}

	/**
	 * Compute the LitInfo for a mixed Literal.
	 */
	public LitInfo colorMixedLiteral(DPLLAtom atom) {
		LitInfo info = m_LiteralInfos.get(atom);

		assert info == null;

		ArrayList<SharedTerm> subterms = new ArrayList<SharedTerm>();
		if (atom instanceof CCEquality) {
			CCEquality eq = (CCEquality)atom;
			subterms.add(eq.getLhs().getFlatTerm());
			subterms.add(eq.getRhs().getFlatTerm());
		} else {
			LinVar lv = null;
			if (atom instanceof BoundConstraint) {
				lv = ((BoundConstraint) atom).getVar();
			} else if (atom instanceof LAEquality) {
				lv = ((LAEquality) atom).getVar();
			}
			Collection<LinVar> components;
			if (lv.isInitiallyBasic()) {
				components = lv.getLinTerm().keySet();
			} else {
				components = Collections.singleton(lv);
			}
			for (LinVar c : components) {
				subterms.add(c.getFlatTerm());
			}
		}
		info = computeMixedOccurrence(subterms);
		this.m_LiteralInfos.put(atom, info);
		
		if (info.getFirstColor() <= info.getLastColor())
			return info;

//		if (atom instanceof CCEquality) {
			info.m_MixedVar = m_Theory.createFreshTermVariable("litaux",
				subterms.get(0).getSort());//klappt das so, mit der Sort?
//		} else {
//			LinVar lv = null;
//			if(atom instanceof BoundConstraint) 
//				lv = ((BoundConstraint) atom).getVar();
//			else
//				lv = ((LAEquality) atom).getVar();
//			info.m_MixedVar = getAuxVarOfLinVar(lv);
//		}
		
		if (atom instanceof CCEquality) {
			CCEquality eq = (CCEquality)atom;
			info.m_MixedAOnLeft = m_SymbolPartition.get(eq.getLhs().getFlatTerm())
					.getLastColor() < info.m_FirstColor;
		} else if (atom instanceof BoundConstraint || atom instanceof LAEquality) {
			LinVar lv = null;
			if(atom instanceof BoundConstraint) 
				lv = ((BoundConstraint) atom).getVar();
			else
				lv = ((LAEquality) atom).getVar();

			info.m_APart = new MutableAffinTerm
				[info.getFirstColor() - info.getLastColor()];
			
//			matLV.add(Rational.ONE, lv);	

			for (int part = info.getLastColor(); 
					part < info.getFirstColor(); part++) {
			
				MutableAffinTerm sumApart = new MutableAffinTerm();	
				
				for(Entry<LinVar, BigInteger> en : lv.getLinTerm().entrySet()) {
					Occurrence occ = 
							m_SymbolPartition.get(
									en.getKey().getFlatTerm());

					if (occ.isALocal(part)) {
						Rational coeff = 
								Rational.valueOf(en.getValue(), BigInteger.ONE);
						sumApart.add(coeff, en.getKey());
//						sumsort = en.getKey().getFlatTerm().getSort();//TODO hack..?
					}
				}
				
				info.m_APart[part-info.getLastColor()] = sumApart;				
//				MutableAffinTerm matALocal = new MutableAffinTerm();
//				Iterator<Map.Entry<SharedTerm, Rational>> it = 
//						matLV.getSummands().entrySet().iterator();
//				while (it.hasNext()) {
//					Map.Entry<SharedTerm, Rational> en = it.next();
//					if(m_SymbolPartition.get(en.getKey()).isALocal(part)) 
//						matALocal.add(en.getValue(), en.getKey());
//				}
//				info.m_APart[part-info.getLastColor()] = matALocal;
			}
		}

		
		return info;
	}

	HashMap<LinVar, TermVariable> m_LinVarToAuxVar = new HashMap<LinVar, TermVariable>();
	
	TermVariable getAuxVarOfLinVar(LinVar lv) {
		TermVariable av = m_LinVarToAuxVar.get(lv);
		if (av == null) {//FIXME: retrieve correct sort for auxVar
			av = m_Theory.createFreshTermVariable("lvAux", m_Theory.getRealSort());
			m_LinVarToAuxVar.put(lv, av);
			return av;
		} else {
			return av;
		}
	}

	private LitInfo computeMixedOccurrence(ArrayList<SharedTerm> subterms) {
		LitInfo info;
		int firstColor = -1;
		int lastColor = Integer.MAX_VALUE;
		for(SharedTerm st : subterms) {
			Occurrence occInfo = getOccurrence(st);
			firstColor = Math.max(firstColor, occInfo.getFirstColor());
			lastColor = Math.min(lastColor, occInfo.getLastColor());
		}
		info = new LitInfo(firstColor, lastColor);
		return info;
	}

	Interpolant mixedPivotRuleReal(Interpolant leqItp, Interpolant sgItp,
			TermVariable mixedVar) {
		Interpolant newI = new Interpolant(leqItp.m_term);

		newI.m_mixedVarToEQs = new HashMap<TermVariable, HashSet<EQInfo>>();
		addAllHashMapSets(newI.m_mixedVarToEQs, leqItp.m_mixedVarToEQs);
		addAllHashMapSets(newI.m_mixedVarToEQs, sgItp.m_mixedVarToEQs);
		newI.m_mixedVarToEQs.remove(mixedVar);
		newI.m_EQToVar = new HashMap<EQInfo, TermVariable>(leqItp.m_EQToVar);
		newI.m_EQToVar.putAll(sgItp.m_EQToVar);

		HashSet<EQInfo> eq1s = leqItp.m_mixedVarToEQs.get(mixedVar); //richtigrum?? L/R?
		HashSet<EQInfo> eq2s = sgItp.m_mixedVarToEQs.get(mixedVar);
		for (EQInfo eq1 : eq1s) {
			Term currentI2Term = sgItp.m_term; 
			newI.m_EQToVar.remove(eq1);

			for (EQInfo eq2 : eq2s) {
				newI.m_EQToVar.remove(eq2);
				TermVariable currentEQ3TV = m_Theory.createFreshTermVariable(
						"EQ3", m_Theory.getBooleanSort());

				//retrieve c1,c2,s2,s2
				InterpolatorAffineTerm s1 = new InterpolatorAffineTerm(eq1.m_t);
				Rational               c1 = s1.getSummands().remove(mixedVar);
				InterpolatorAffineTerm s2 = new InterpolatorAffineTerm(eq2.m_t);
				Rational               c2 = s2.getSummands().remove(mixedVar);
				assert (c1.signum() * c2.signum() == -1);
				InfinitNumber newK = eq1.m_k.mul(c2.abs())
						.add(eq2.m_k.mul(c1.abs()));

				//compute c1s2 + c2s1
				InterpolatorAffineTerm c1s2c2s1 = new InterpolatorAffineTerm();
				c1s2c2s1.add(c1.abs(), s2);
				c1s2c2s1.add(c2.abs(), s1);

				//compute s2/c2
				InterpolatorAffineTerm s2divc2 = new InterpolatorAffineTerm(s2);
				s2divc2.mul(c2.inverse().negate());
				Term s2DivByc2 = s2divc2.toSMTLib(m_Theory, false);
				Term newF = m_Theory.TRUE;
				if (eq1.m_k.equals(InfinitNumber.ZERO)) {
					newF = m_Theory.and(newF, substitute(eq1.m_F, s2DivByc2, mixedVar));
				}
				if (eq2.m_k.equals(InfinitNumber.ZERO)) {
					newF = m_Theory.and(newF, substitute(eq2.m_F, s2DivByc2, mixedVar));
				}
				if (newF != m_Theory.TRUE) {
					newF = m_Theory.and(
							c1s2c2s1.toLeq0(m_Theory),
							newF);
					newK = InfinitNumber.ZERO;
				} else
					newF = m_Theory.FALSE;
				EQInfo eq3 = new EQInfo(c1s2c2s1, newK, newF);

				newI.m_EQToVar.put(eq3, currentEQ3TV);


				for (HashSet<EQInfo> set : newI.m_mixedVarToEQs.values()) {
					if (set.contains(eq1)) {
						set.remove(eq1);
						set.add(eq3);
					}
					if (set.contains(eq2)) {
						set.remove(eq2);
						set.add(eq3);
					}
				}

				currentI2Term = substitute(currentI2Term, currentEQ3TV, sgItp.m_EQToVar.get(eq2));


			}

			newI.m_term = substitute(newI.m_term, currentI2Term, leqItp.m_EQToVar.get(eq1));
		}
		return newI;
	}

	Interpolant mixedPivotRuleInt(Interpolant leqItp, Interpolant sgItp,
			TermVariable mixedVar) {
		Interpolant newI = new Interpolant(leqItp.m_term);
		newI.m_mixedVarToEQs = new HashMap<TermVariable, HashSet<EQInfo>>();
		addAllHashMapSets(newI.m_mixedVarToEQs, leqItp.m_mixedVarToEQs);
		addAllHashMapSets(newI.m_mixedVarToEQs, sgItp.m_mixedVarToEQs);
		newI.m_mixedVarToEQs.remove(mixedVar);
		newI.m_EQToVar = new HashMap<EQInfo,TermVariable>(leqItp.m_EQToVar);
		newI.m_EQToVar.putAll(sgItp.m_EQToVar);

		HashSet<EQInfo> eq1s = leqItp.m_mixedVarToEQs.get(mixedVar);
		HashSet<EQInfo> eq2s = sgItp.m_mixedVarToEQs.get(mixedVar);
		for (EQInfo eq1 : eq1s) {
			newI.m_EQToVar.remove(eq1);
			Term currentI2Term = sgItp.m_term; 

			for (EQInfo eq2 : eq2s) {
				newI.m_EQToVar.remove(eq2);
				TermVariable currentEQ3TV = m_Theory.createFreshTermVariable(
						"EQ3", m_Theory.getBooleanSort());

				//retrieve c1,c2,s1,s2
				InterpolatorAffineTerm s1 = new InterpolatorAffineTerm(eq1.m_t);
				Rational               c1 = s1.getSummands().remove(mixedVar);
				InterpolatorAffineTerm s2 = new InterpolatorAffineTerm(eq2.m_t);
				Rational               c2 = s2.getSummands().remove(mixedVar);
				assert (c1.isIntegral() && c2.isIntegral());
				assert (c1.signum() * c2.signum() == -1);
				Rational absc1 = c1.abs();
				Rational absc2 = c2.abs();

				//compute c1s2 + c2s1
				InterpolatorAffineTerm c1s2c2s1 = new InterpolatorAffineTerm();
				c1s2c2s1.add(absc1, s2);
				c1s2c2s1.add(absc2, s1);

				//compute newk = c2k1 + c1k2 + c1c2;
				Rational c1c2 = absc1.mul(absc2);
				InfinitNumber newK = eq1.m_k.mul(absc2).add(eq2.m_k.mul(absc1))
						.add(new InfinitNumber(c1c2, 0));
				assert (newK.isIntegral());
				
				Term newF = m_Theory.FALSE;
				Rational theC;
				InterpolatorAffineTerm theS;
				if (absc1.compareTo(absc2) > 0) {
					theC = c1;
					theS = s1;
				} else {
					theC = c2;
					theS = s2;
				}
				BigInteger cNum = theC.abs().numerator();
				// Use -s/c as start value.
				InterpolatorAffineTerm sPlusOffset = new InterpolatorAffineTerm();
				sPlusOffset.add(theC.signum() > 0 ? Rational.MONE : Rational.ONE, theS);
				Rational offset = Rational.ZERO;
				if (theC.signum() < 0)
					sPlusOffset.add(theC.abs().add(Rational.MONE));
				while (offset.compareTo(newK.ma) <= 0) {
					Term x;
					x = sPlusOffset.toSMTLib(m_Theory, true);
					if (!cNum.equals(BigInteger.ONE))
						x = m_Theory.term("div", x, m_Theory.numeral(cNum));
					InterpolatorAffineTerm ineq1 = 
							new InterpolatorAffineTerm(s1);
					ineq1.add(c1, x);
					ineq1.add(eq1.m_k);
					ineq1.m_constant = ineq1.m_constant.floor();
					ineq1.add(Rational.ONE);
					Term smtIneq1 = ineq1.toLeq0(m_Theory);
					InterpolatorAffineTerm ineq2 = 
							new InterpolatorAffineTerm(s2);
					ineq2.add(c2, x);
					ineq2.add(eq2.m_k);
					ineq2.m_constant = ineq2.m_constant.floor();
					ineq2.add(Rational.ONE);
					Term smtIneq2 = ineq2.toLeq0(m_Theory);
					
					if (theS == s1) {
						//ineq1 = s1 + c1*((-s1 + offset) div c1) < -k1 
						//        s1 + -s1+k - (k-s1 mod c1) < -k1
						//        offset - (.. mod c1) < -k1
						//        offset + k1 < (.. mod c1)
						Rational diff = offset.add(eq1.m_k.ma);
						if (diff.signum() < 0)
							smtIneq1 = m_Theory.TRUE;
						else if (diff.compareTo(absc1) > 0)
							smtIneq1 = m_Theory.FALSE;
					} else {
						Rational diff = offset.add(eq2.m_k.ma);
						if (diff.signum() < 0)
							smtIneq2 = m_Theory.TRUE;
						else if (diff.compareTo(absc2) > 0)
							smtIneq2 = m_Theory.FALSE;
					}					
					Term F = m_Theory.and(
							m_Theory.or(smtIneq1,
									substitute(eq1.m_F, x, mixedVar)),
							m_Theory.or(smtIneq2,
									substitute(eq2.m_F, x, mixedVar)));
					newF = m_Theory.or(newF, F);
					sPlusOffset = sPlusOffset.add(theC.negate());
					offset = offset.add(c1c2);
				}
				
				EQInfo eq3 = new EQInfo(c1s2c2s1, newK, newF);

				newI.m_EQToVar.put(eq3, currentEQ3TV);

				//plan: in mixedVarToEQs alle values durchgehen, und wo immer eq1 oder eq2 im 
				//betreffenden set auftaucht durch eq3 ersetzen.
				//außerdem den key mit der mixedvar löschen (einmal ganz am Anfang)
				for (HashSet<EQInfo> set : newI.m_mixedVarToEQs.values()) {
					if (set.contains(eq1)) {
						set.remove(eq1);
						set.add(eq3);
					}
					if (set.contains(eq2)) {
						set.remove(eq2);
						set.add(eq3);
					}
				}
				currentI2Term = substitute(currentI2Term, currentEQ3TV, sgItp.m_EQToVar.get(eq2));
			}

			newI.m_term = substitute(newI.m_term, currentI2Term, leqItp.m_EQToVar.get(eq1));
		}
		return newI;
	}

	public Interpolant mixedPivotLA(Interpolant leqItp,
			Interpolant sgItp, TermVariable mixedVar) {
		if (mixedVar.getSort().getName().equals("Real"))
			return mixedPivotRuleReal(leqItp, sgItp, mixedVar);
		else
			return mixedPivotRuleInt(leqItp, sgItp, mixedVar);
	}
}


