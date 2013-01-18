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

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.Occurrence;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAppTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCBaseTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;


public class CCInterpolator {
	
	Interpolator m_Interpolator;
	
	HashMap<SymmetricPair<CCTerm>, PathInfo> m_Paths;
	
	Theory m_Theory;
	int m_numInterpolants;
	
	Set<Term>[] m_Interpolants;
	

	class PathInfo {
		CCTerm[] m_Path;
		CCEquality[] m_Lits;
		
		int m_MaxColor;
		PathEnd m_Head, m_Tail;

		/* max color is the maximum of all firstColor of all literals on the
		 * path.
		 * 
		 * Head color is the lastColor of the first literal before the first
		 * path change.  If head color >= max color, then there is no path
		 * change.
		 * 
		 */
		boolean m_Computed;

		class PathEnd {
			int         m_Color;
			Term[]      m_Term;
			Set<Term>[] m_Pre;
			
			@SuppressWarnings("unchecked")
			public PathEnd(int color) {
				m_Color = color;
				m_Term = new Term[m_numInterpolants];
				m_Pre = new Set[m_numInterpolants];
			}

			/**
			 * 
			 */
			public void closeAPath(PathEnd other, Term boundaryTerm, int firstColor) {
				int oldmax = m_MaxColor;
				if (m_MaxColor < firstColor) {
					if (m_Color > m_MaxColor)
						m_Color = m_MaxColor;
					m_MaxColor = firstColor;
				}
				while (m_Color < firstColor) {
					if (m_Color < oldmax) {
						addPre(m_Color, m_Theory.equals(boundaryTerm, m_Term[m_Color]));
						addInterpolantClause(m_Color, m_Pre[m_Color]);
						m_Pre[m_Color] = null;
						m_Term[m_Color] = null;
					} else {
						if (other.m_Color > m_Color)
							other.m_Color = m_Color;
						other.m_Term[m_Color] = boundaryTerm;
						if (m_Pre[m_Color] != null) {
							other.m_Pre[m_Color] = m_Pre[m_Color];
							m_Pre[m_Color] = null;
						}
					}
					m_Color++;
				}
			}
			
			public void closeBPath(Term boundaryTerm, int lastColor) {
				while (m_Color > lastColor) {
					m_Color--;
					if (m_Color < m_MaxColor) {
						/* Close B paths: start A path  */
						m_Term[m_Color] = boundaryTerm;
					}
				}
			}

			public Term getBoundTerm(int color) {
				if (color < m_Color) {
					CCTerm first = this == m_Head ? m_Path[0] 
							: m_Path[m_Path.length -1];
					return first.toSMTTerm(m_Theory);
				} else if (color < m_MaxColor) {
					return m_Term[color];
				} else {
					CCTerm last = this == m_Tail ? m_Path[0] 
							: m_Path[m_Path.length -1];
					return last.toSMTTerm(m_Theory);
				}
			}
			
			public void addPre(int color, Term pre) {
				if (m_Pre[color] == null)
					m_Pre[color] = new HashSet<Term>();
				m_Pre[color].add(pre);
			}
			
			public void addAllPre(int color, PathEnd src) {
				Set<Term> pre = src.m_Pre[color];
				if (pre == null)
					return;
				if (m_Pre[color] == null)
					m_Pre[color] = new HashSet<Term>();
				m_Pre[color].addAll(pre);
			}
			
			private void mergeCongPath(PathEnd other, CCAppTerm start, CCAppTerm end) {
				CCTerm term = start.getFunc();
				while (term instanceof CCAppTerm) {
					term = ((CCAppTerm) term).getFunc();
				}
				Occurrence rightOccur = 
						m_Interpolator.getOccurrence(end.getFlatTerm());
				FunctionSymbol func = ((CCBaseTerm)term).getFunctionSymbol();
				int numArgs = func.getParameterCount();
				PathInfo[] argPaths = new PathInfo[numArgs];
				PathEnd[] head = new PathEnd[numArgs];
				PathEnd[] tail = new PathEnd[numArgs];
				boolean[] isReverse = new boolean[numArgs];
				int arg = numArgs;
				while (true) {
					arg--;
					argPaths[arg] =  
						start.getArg() == end.getArg() ? new PathInfo(start.getArg())
					  : m_Paths.get(new SymmetricPair<CCTerm>(start.getArg(), end.getArg()));
					argPaths[arg].interpolatePathInfo();
					isReverse[arg] = !(start.getArg() == argPaths[arg].m_Path[0]);
					head[arg] = isReverse[arg] ? argPaths[arg].m_Tail : argPaths[arg].m_Head;
					tail[arg] = isReverse[arg] ? argPaths[arg].m_Head : argPaths[arg].m_Tail;
					Term startTerm = start.getArg().toSMTTerm(m_Theory);
					head[arg].closeAPath(tail[arg], startTerm, m_Color);
					head[arg].closeBPath(startTerm, m_Color);
					if (arg == 0)
						break;
					
					start = (CCAppTerm) start.getFunc();
					end = (CCAppTerm) end.getFunc();
				}
				
				int litfirst = rightOccur.getFirstColor();
				while (m_Color < litfirst) {
					Term[] boundaryParams = new Term[numArgs];
					for (int i = 0; i < numArgs; i++) {
						boundaryParams[i] = head[i].getBoundTerm(m_Color);
						addAllPre(m_Color, tail[i]);
					}
					Term boundaryTerm = m_Theory.term(func, boundaryParams);
					closeAPath(other, boundaryTerm, m_Color+1);
				}
				int litlast = rightOccur.getLastColor();
				int highColor = m_Color;
				while (m_Color > litlast) {
					Term[] boundaryParams = new Term[numArgs];
					for (int i = 0; i < numArgs; i++) {
						boundaryParams[i] = tail[i].getBoundTerm(m_Color-1);
						addAllPre(m_Color-1, tail[i]);
					}
					Term boundaryTerm = m_Theory.term(func, boundaryParams);
					closeBPath(boundaryTerm, m_Color-1);
				}
				for (int i = 0; i < numArgs; i++) {
					Term boundTerm = tail[i].getBoundTerm(-1);
					tail[i].closeAPath(tail[i], boundTerm, m_Color);
					tail[i].closeBPath(boundTerm, m_Color);
					for (int color = highColor; 
							color < m_numInterpolants; color++) {
						if (color < argPaths[i].m_MaxColor)
							addPre(color, m_Theory.distinct(head[i].getBoundTerm(color),
									tail[i].getBoundTerm(color)));
						addAllPre(color, head[i]);
						addAllPre(color, tail[i]);
					}
				}
			}
			
			public String toString() {
				StringBuilder sb = new StringBuilder();
				String comma = "";
				sb.append(m_Color).append(":[");
				for (int i = m_Color; i < m_MaxColor; i++) {
					sb.append(comma);
					if (m_Pre[i] != null)
						sb.append(m_Pre[i]).append(" or ");
					sb.append(m_Term[i]);
					comma = ",";
				}
				comma = "|";
				for (int i = m_MaxColor; i < m_numInterpolants; i++) {
					if (m_Pre[i] != null) {
						sb.append(comma).append("pre").append(i).append(":");
						sb.append(m_Pre[i]);
						comma = ",";
					}
				}
				sb.append("]");
				return sb.toString();
			}
		}		
		
		/* invariants:
		 *  HeadTerm[p] != null exactly for p in [m_HeadColor, m_MaxColor-1]
		 *  HeadPre[p] != null only for p in [m_HeadColor, numInterpolants]
		 *  HeadColor is in between first and last color of head term.
		 *  likewise for Tail.
		 *  MaxColor is maximum of all first of all terms and literals
		 *  involved in current path (but there may be bigger literals in
		 *  congruence paths that were added to headPre/tailPre).
		 *  
		 *  The partial interpolant of the current path is 
		 *    m_Interpolants &&
		 *       HeadPre ==> Lits[0] == m_HeadTerm && 
		 *       TailPre ==> m_TailTerm == lits[n]
		 *  where HeadTerm = Lits[0] for partitions < HeadColor and
		 *        TailTerm = Lits[n] for partitions < TailColor.
		 *
		 *  For partitions >= maxColor, everything so far was in A, so
		 *  the partial interpolant of the current path is 
		 *    m_Interpolants &&
		 *       TailPre ==> Lits[0] == lits[n]
		 */
		
		public PathInfo(CCTerm[] path, CCEquality[] litsOnPath) {
			m_Path = path;
			m_Lits = litsOnPath;
		}
		
		public PathInfo(CCTerm arg) {
			m_Path = new CCTerm[] { arg };
			m_Lits = new CCEquality[0];
		}

		public void interpolatePathInfo() {
			if (m_Computed)
				return;
			Occurrence headOccur = 
					m_Interpolator.getOccurrence(m_Path[0].getFlatTerm());
			int lastColor = headOccur.getLastColor();
			m_Head = new PathEnd(lastColor);
			m_Tail = new PathEnd(lastColor);
			m_MaxColor = headOccur.getFirstColor();
			
			for (int i = 0; i < m_Lits.length; i++) {
				if (m_Lits[i] == null) {
					CCAppTerm left = (CCAppTerm) m_Path[i];
					CCAppTerm right = (CCAppTerm) m_Path[i+1];
					m_Tail.mergeCongPath(m_Head, left, right);
				} else {
					LitInfo info = m_Interpolator.getLiteralInfo(m_Lits[i]);
					Term boundaryTerm;
					int litfirst = info.getFirstColor();
					int litlast  = info.getLastColor();
					boundaryTerm = m_Path[i].toSMTTerm(m_Theory);
					if (info.isMixed(litlast)) {
						if ((m_Lits[i].getLhs() == m_Path[i]) == info.isAOnLeft()) {
							m_Tail.closeAPath(m_Head, boundaryTerm, litlast);
							litlast = litfirst;
						} else {
							m_Tail.closeBPath(boundaryTerm, litfirst);
							litfirst = litlast;
						}
						boundaryTerm = 
							computeIntermediateTerm(m_Lits[i], info.getMixedVar());
					}
					m_Tail.closeAPath(m_Head, boundaryTerm, litfirst);
					m_Tail.closeBPath(boundaryTerm, litlast);
				}
			}
			m_Computed= true; 
		}

		/**
		 * Build an interpolant clause and add it to the interpolant set.
		 * @param pre  The disequalities summarizing the requirements from
		 *             the B-part in skipped argument paths.
		 * @param lhsTerm The end of the A-equality chain. 
		 * @param rhsTerm The start of the A-equality chain.
		 * @param isNegated True, if there is a disequality in the chain.
		 */
		private void addInterpolantClause(int color, Set<Term> pre) {
			Term clause = pre == null ? m_Theory.FALSE
						: m_Theory.or(pre.toArray(new Term[pre.size()]));
			m_Interpolants[color].add(clause);
		}

		private Term computeIntermediateTerm(CCEquality cceq,
				TermVariable mixedVar) {
			return mixedVar;
		}
		
		public String toString() {
			return "PathInfo["+Arrays.toString(m_Path)+","
					+ m_Head + ',' + m_Tail + "," + m_MaxColor+"]";
		}

		public void addDiseq(CCEquality diseq) {
			LitInfo info = m_Interpolator.getLiteralInfo(diseq);
			Term boundaryTailTerm, boundaryHeadTerm;
			int litfirst = info.getFirstColor();
			int litlast  = info.getLastColor();
			boundaryHeadTerm = m_Path[0].toSMTTerm(m_Theory);
			if (info.isMixed(litlast)) {
				// Put the A part of the equation to the tail.
				if ((diseq.getLhs() == m_Path[m_Path.length-1]) != info.isAOnLeft()) {
					reversePath();
					boundaryTailTerm = boundaryHeadTerm;
					boundaryHeadTerm = m_Path[m_Path.length-1].toSMTTerm(m_Theory);
				} else {
					boundaryTailTerm = m_Path[m_Path.length-1].toSMTTerm(m_Theory);
				}
				m_Tail.closeAPath(m_Head, boundaryTailTerm, litlast);
				boundaryTailTerm = 
					computeIntermediateTerm(diseq, info.getMixedVar());
				litlast = litfirst;
			} else {
				boundaryTailTerm = m_Path[m_Path.length-1].toSMTTerm(m_Theory);
			}
			m_Tail.closeAPath(m_Head, boundaryTailTerm, litfirst);
			m_Tail.closeBPath(boundaryTailTerm, litlast);
			m_Head.closeAPath(m_Tail, boundaryHeadTerm, litfirst);
			m_Head.closeBPath(boundaryHeadTerm, litlast);
		}

		private void reversePath() {
			PathEnd temp = m_Head;
			m_Head = m_Tail;
			m_Tail = temp;
		}

		public void close() {
			for (int color = Math.min(m_Head.m_Color, m_Tail.m_Color);
					color < m_MaxColor; color++) {
				m_Tail.addAllPre(color, m_Head);
				m_Head.m_Pre[color] = null;
				m_Tail.addPre(color, m_Theory.distinct
					(m_Tail.getBoundTerm(color), m_Head.getBoundTerm(color)));
				addInterpolantClause(color, m_Tail.m_Pre[color]);
			}
			for (int color = m_MaxColor; color < m_numInterpolants; color++) {
				assert (m_Head.m_Pre[color] == null);
				addInterpolantClause(color, m_Tail.m_Pre[color]);
			}
		}
	}
	
	@SuppressWarnings("unchecked")
	public CCInterpolator(Interpolator ipolator) {
		m_Interpolator = ipolator;
		m_numInterpolants = ipolator.m_NumInterpolants;
		m_Theory = ipolator.m_Theory;
		m_Paths = new HashMap<SymmetricPair<CCTerm>, PathInfo>();
		m_Interpolants = new Set[m_numInterpolants];
		for (int i = 0; i < m_numInterpolants; i++)
			m_Interpolants[i] = new HashSet<Term>();
	}
	
	public Term[] computeInterpolants(CCAnnotation annot) {
		PathInfo mainPath = null; 
		CCTerm[][] paths = annot.getPaths();
		CCEquality[][] lits = annot.getLitsOnPaths();
		for (int i = 0; i < paths.length; i++) {
			CCTerm first = paths[i][0];
			CCTerm last = paths[i][paths[i].length-1];
			PathInfo pathInfo = new PathInfo(paths[i], lits[i]);
			m_Paths.put(new SymmetricPair<CCTerm>(first, last), 
					pathInfo);
			if (i == 0)
				mainPath = pathInfo;
		}
		mainPath.interpolatePathInfo();
		CCEquality diseq = annot.getDiseq();
		if (diseq != null)
			mainPath.addDiseq(diseq);
		mainPath.close();
		Term[] interpolants = new Term[m_numInterpolants];
		for (int i = 0; i < m_numInterpolants; i++) {
			interpolants[i] = m_Theory.and
				(m_Interpolants[i].toArray(new Term[m_Interpolants[i].size()]));
		}
		return interpolants;
	}
	
	public String toString() {
		return Arrays.toString(m_Interpolants); 
	}
}
