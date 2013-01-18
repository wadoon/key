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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.MutableRational;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;



/**
 *  Represents a modifiable affin term, i.e. SUM_i c_i * x_i + c, 
 *  where the x_i are initially nonbasic variable.
 *    
 *  @author hoenicke.
 */
public class MutableAffinTerm {
	Map<SharedTerm, Rational> m_summands =
		new HashMap<SharedTerm, Rational>();
	InfinitNumber m_constant;
	
	public MutableAffinTerm() {
		m_constant = InfinitNumber.ZERO;
	}

	public MutableAffinTerm(Map<SharedTerm, Rational> sum, boolean isInt) {
		m_constant = InfinitNumber.ZERO;
		m_summands.putAll(sum);
	}

	public MutableAffinTerm(LinTerm term, boolean isInt) {
		m_constant = InfinitNumber.ZERO;
		addBigIntMap(Rational.ONE, term.mcoeffs);
	}

	public MutableAffinTerm add(Rational c) {
		m_constant = m_constant.add(new InfinitNumber(c, 0));
		return this;
	}
	
	public MutableAffinTerm add(InfinitNumber c) {
		m_constant = m_constant.add(c);
		return this;
	}
	public MutableAffinTerm add(Rational c, SharedTerm term) {
		if (c.equals(Rational.ZERO))
			return this;
		if (term instanceof SharedAffineTerm)
			add(c, ((SharedAffineTerm) term).toAffineTerm().getMutableAffinTerm());
		else
			addSimple(c, term);
		return this;
	}
	public MutableAffinTerm add(Rational c, LinVar var) {
		if (c.equals(Rational.ZERO))
			return this;
		if (var.isInitiallyBasic()) {
			for (Map.Entry<LinVar, BigInteger> me : var.getLinTerm().entrySet())
				add(c.mul(me.getValue()), me.getKey());
		} else {
			addSimple(c, var.getFlatTerm());
		}
		return this;
	}

	private void addMap(Rational c, Map<SharedTerm, Rational> linterm) {
		for (Map.Entry<SharedTerm, Rational> summand : linterm.entrySet())
			addSimple(c.mul(summand.getValue()), summand.getKey());
	}
	
	private void addBigIntMap(Rational c, Map<LinVar, BigInteger> linterm) {
		for (Map.Entry<LinVar, BigInteger> summand : linterm.entrySet())
			addSimple(c.mul(summand.getValue()), summand.getKey().getFlatTerm());
	}
	
	private void addSimple(Rational c, SharedTerm term) {
		assert (/*!term.getLinVar().isInitiallyBasic() &&*/ !c.equals(Rational.ZERO));
		Rational oldc = m_summands.remove(term);
		if (oldc != null) {
			c = oldc.add(c);
			if (c.equals(Rational.ZERO))
				return;
		}
		m_summands.put(term,c);
	}

	public MutableAffinTerm add(Rational c, MutableAffinTerm a) {
		if (c != Rational.ZERO) {
			addMap(c, a.m_summands);
			m_constant = m_constant.add(a.m_constant.mul(c));
		}
		return this;
	}

	public MutableAffinTerm mul(Rational c) {
		if (c.equals(Rational.ZERO))
			m_summands.clear();
		else if (!c.equals(Rational.ONE)) {
			for (Map.Entry<SharedTerm, Rational> summand : m_summands.entrySet()) {
				summand.setValue(c.mul(summand.getValue()));
			}
			m_constant = m_constant.mul(c);
		}
		return this;
	}
	
	public MutableAffinTerm div(Rational c) {
		return mul(c.inverse());
	}
	public MutableAffinTerm negate() {
		return mul(Rational.MONE);
	}
	public boolean isConstant() {
		return m_summands.isEmpty();
	}
	public InfinitNumber getConstant() {
		return m_constant;
	}
	public Map<SharedTerm,Rational> getSummands() {
		return m_summands;
	}
	
	public Rational getGCD() {
		assert (!m_summands.isEmpty());
		Iterator<Rational> it = m_summands.values().iterator();
		Rational gcd = it.next(); 
		boolean firstSign = gcd.isNegative();
		gcd = gcd.abs();
		while (it.hasNext()) {
			gcd = gcd.gcd(it.next().abs());
		}
		if (firstSign)
			gcd = gcd.negate();
		return gcd;
	}
	
	/**
	 * For integer valued interpolants, convert Rationals to integer valued
	 * Rational by dividing by the rational greatest common divisor.
	 */
	void normalize() {
		mul(getGCD().inverse());
	}

	public String toString() {
		StringBuilder sb = new StringBuilder();
		boolean isFirst = true;
		for (Entry<SharedTerm,Rational> entry : m_summands.entrySet()) {
			SharedTerm var = entry.getKey();
			Rational fact = entry.getValue();
			if (fact.isNegative()) {
				sb.append(isFirst ? "-" : " - ");
			} else {
				sb.append(isFirst ? "" : " + ");
			}
			fact = fact.abs();
			if (!fact.equals(Rational.ONE))
				sb.append(fact).append("*");
			sb.append(var);
			isFirst = false;
		}
		if (isFirst)
			sb.append(m_constant);
		else {
			int signum = m_constant.compareTo(InfinitNumber.ZERO); 
			if (signum < 0) {
				sb.append(" - ");
				sb.append(m_constant.mul(Rational.MONE));
			} else if (signum > 0){
				sb.append(" + ");
				sb.append(m_constant);
			}
		}
		return sb.toString();
	}
	
	public Sort getSort(Theory t) {
		return isInt() ? t.getSort("Int") : t.getSort("Real");
	}

	/**
	 * Convert the affine term to a term in our core theory.
	 */ 
	public Term toSMTLib(Theory t, boolean isInt, boolean useAuxVars) {
		assert(m_constant.meps == 0);
		Sort numSort = isInt ? t.getSort("Int") : t.getSort("Real");
		assert(numSort != null);
		Sort[] binfunc = new Sort[] {numSort,numSort};
		FunctionSymbol times = t.getFunction("*",binfunc);
		FunctionSymbol plus = t.getFunction("+",binfunc);
		FunctionSymbol negate = t.getFunction("-", numSort);
		if (negate == null)
			negate = t.getFunction("-", numSort);
		assert (!isInt || m_constant.ma.isIntegral());
		Term comb = m_constant.ma.equals(Rational.ZERO) ? null 
				: isInt ? t.numeral(m_constant.ma.numerator())
				: t.rational(m_constant.ma.numerator(), m_constant.ma.denominator());
		for (Map.Entry<SharedTerm,Rational> me : m_summands.entrySet()) {
			SharedTerm lv = me.getKey();
			Term convme = lv.getSMTTerm(useAuxVars);
			// if affine term is integral it may only add integers.
			assert (!isInt || lv.getSort().getName().equals("Int"));
			assert (!isInt || me.getValue().isIntegral());
			if (!isInt && lv.getSort().getName().equals("Int")) {
				Sort intSort = t.getSort("Int");
				FunctionSymbol toReal = t.getFunction("to_real", intSort);
				convme = t.term(toReal, convme);
			}
			if (me.getValue().equals(Rational.MONE)) {
				convme = t.term(negate, convme);
			} else if (!me.getValue().equals(Rational.ONE)) {
				Term convfac = isInt ? t.numeral(me.getValue().numerator())
						: t.rational(me.getValue().numerator(),me.getValue().denominator());
				convme = t.term(times, convfac, convme);
			}
			if (comb == null)
				comb = convme;
			else
				comb = t.term(plus, convme, comb);
		}
		if (comb == null)
			return isInt ? t.numeral(BigInteger.ZERO) : t.rational(BigInteger.ZERO, BigInteger.ONE);
		return comb;
	}
	
	public Rational getValue(LinArSolve linar) {
		assert m_constant.meps == 0;
		MutableRational val = new MutableRational(m_constant.ma);
		for (Map.Entry<SharedTerm, Rational> me : m_summands.entrySet()) {
			val.add(me.getValue().mul(linar.realValue(me.getKey().getLinVar())));
		}
		return val.toRational();
	}
	
	public boolean isInt() {
		for (SharedTerm v : m_summands.keySet())
			if (!v.getSort().getName().equals("Int"))
				return false;
		return true;
	}
	
	/**
	 * Create the term <code>this <= val</code>.
	 * @param t   Theory used in conversion.
	 * @return A term for <code>this <= val</code>.
	 */
	public Term toLeq0(Theory t) {
		assert m_constant.meps >= 0;
		if (isConstant())
			return m_constant.compareTo(InfinitNumber.ZERO) <= 0 ? t.TRUE : t.FALSE; 
		boolean isInt = isInt();
		Sort numSort = isInt ? t.getSort("Int") : t.getSort("Real");
		assert(numSort != null);
		Sort[] binfunc = new Sort[] {numSort,numSort};
		FunctionSymbol times = t.getFunction("*",binfunc);
		FunctionSymbol plus = t.getFunction("+",binfunc);
		assert (!isInt || m_constant.ma.isIntegral());
		ArrayList<Term> lcomb = new ArrayList<Term>();
		ArrayList<Term> rcomb = new ArrayList<Term>();
		for (Map.Entry<SharedTerm,Rational> me : m_summands.entrySet()) {
			SharedTerm lv = me.getKey();
			Term convme = lv.getSMTTerm();
			// if affine term is integral it may only add integers.
			assert (!isInt || lv.getSort().getName().equals("Int"));
			assert (!isInt || me.getValue().isIntegral());
			if (!isInt && lv.getSort().getName().equals("Int")) {
				Sort intSort = t.getSort("Int");
				FunctionSymbol toReal = t.getFunction("to_real", intSort);
				convme = t.term(toReal, convme);
			}
			if (me.getValue().equals(Rational.MONE))
				rcomb.add(convme);
			else if (me.getValue().signum() < 0) {
				Rational cf = me.getValue().abs();
				Term convfac = isInt ? t.numeral(cf.numerator())
						: t.rational(cf.numerator(),cf.denominator());
				rcomb.add(t.term(times, convfac, convme));
			} else if (me.getValue().equals(Rational.ONE))
				lcomb.add(convme);
			else if (me.getValue().signum() > 0) {
				Rational cf = me.getValue();
				Term convfac = isInt ? t.numeral(cf.numerator())
						: t.rational(cf.numerator(),cf.denominator());
				lcomb.add(t.term(times, convfac, convme));
			}
		}
		if (!m_constant.ma.equals(Rational.ZERO)) 
			rcomb.add(isInt ? t.numeral(m_constant.ma.numerator().negate())
			: t.rational(m_constant.ma.numerator().negate(), m_constant.ma.denominator()));
		if (lcomb.isEmpty() && rcomb.isEmpty())
			// We either have 0<=0 or 0<0
			return m_constant.meps == 0 ? t.TRUE : t.FALSE;
		Term tlcomb, trcomb;
		switch (lcomb.size()) {
		case 0:
			tlcomb = isInt ?
				t.numeral(BigInteger.ZERO) : t.decimal(BigDecimal.ZERO);
			break;
		case 1:
			tlcomb = lcomb.get(0);
			break;
		default:
			tlcomb = t.term(plus, lcomb.toArray(new Term[lcomb.size()]));
		}
		switch (rcomb.size()) {
		case 0:
			trcomb = isInt ?
				t.numeral(BigInteger.ZERO) : t.decimal(BigDecimal.ZERO);
			break;
		case 1:
			trcomb = rcomb.get(0);
			break;
		default:
			trcomb = t.term(plus, rcomb.toArray(new Term[rcomb.size()]));
		}				
		return t.term(m_constant.meps == 0 ? "<=" : "<", tlcomb, trcomb);
	}
}
