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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Theory;


public class TermCompiler extends TermTransformer {
	private Term createNot(Term arg) {
		Theory theory = arg.getTheory();
		if (arg == theory.FALSE)
			return theory.TRUE;
		if (arg == theory.TRUE)
			return theory.FALSE;
		if ((arg instanceof ApplicationTerm)
			&& ((ApplicationTerm) arg).getFunction().getName().equals("not"))
			return ((ApplicationTerm) arg).getParameters()[0];
		return theory.term("not", arg);
	}
	private Term createOr(Term... args) {
		HashSet<Term> ctx = new HashSet<Term>();
		Theory theory = args[0].getTheory();
		Term trueTerm = theory.TRUE;
		Term falseTerm = theory.FALSE;
		for (Term t : args) {
			if (t == trueTerm)
				return t;
			if (t != falseTerm) {
				if (ctx.contains(createNot(t)))
					return trueTerm;
				ctx.add(t);
			}
		}
		// Handle disjunctions of false
		if (ctx.size() == 0)
			return theory.FALSE;
		// Handle simplifications to unary or
		if (ctx.size() == 1)
			return ctx.iterator().next();
		return theory.term("or", ctx.size() == args.length ? args :
			ctx.toArray(new Term[ctx.size()]));
	}
	private Term createOr(Term arg1, Term arg2) {
		Theory theory = arg1.getTheory();
		if (arg1 == theory.TRUE || arg2 == theory.TRUE)
			return theory.TRUE;
		if (arg1 == theory.FALSE)
			return arg2;
		if (arg2 == theory.FALSE)
			return arg1;
		if (arg1 == arg2)
			return arg1;
		if (arg1 == createNot(arg2))
			return theory.TRUE;
		return arg1.getTheory().term("or", arg1, arg2);
	}
	private Term createLeq0(SMTAffineTerm arg) {
		return arg.getTheory().term("<=", arg, arg.mul(Rational.ZERO));
	}
	private Term createIte(Term cond, Term trueBranch, Term falseBranch) {
		Theory theory = cond.getTheory();
		if (cond == theory.TRUE)  return trueBranch;
		if (cond == theory.FALSE) return falseBranch;
		if (trueBranch == falseBranch) return trueBranch;
		if (trueBranch == theory.TRUE && falseBranch == theory.FALSE)
			return cond;
		if (trueBranch == theory.FALSE && falseBranch == theory.TRUE)
			return createNot(cond);
		if (trueBranch == theory.TRUE)
			// No need for createOr since we are already sure that we cannot
			// simplify further
			return theory.term("or", cond, falseBranch);
		if (trueBranch == theory.FALSE)
			// /\ !cond falseBranch => !(\/ cond !falseBranch)
			return theory.term("not",
					theory.term("or", cond, createNot(falseBranch)));
		if (falseBranch == theory.TRUE)
			// => cond trueBranch => \/ !cond trueBranch
			return theory.term("or", createNot(cond), trueBranch);
		if (falseBranch == theory.FALSE)
			// /\ cond trueBranch => !(\/ !cond !trueBranch)
			return theory.term("not",
					theory.term("or", createNot(cond), createNot(trueBranch)));
		return theory.term("ite", cond, trueBranch, falseBranch);
	}
	private Term createEq(Term... args) {
		HashSet<Term> tmp = new HashSet<Term>();
		Theory theory = args[0].getTheory();
		if (args[0].getSort().isNumericSort()) {
			Rational lastConst = null;
			for (Term t : args) {
				if (t instanceof ConstantTerm || t instanceof SMTAffineTerm) {
					SMTAffineTerm at = SMTAffineTerm.create(t);
					if (at.isConstant()) {
						if (lastConst == null) {
							lastConst = at.getConstant();
						} else if (!lastConst.equals(at.getConstant()))
							return theory.FALSE;
					}
					tmp.add(at);
				} else
					tmp.add(t);
			}
		} else if (args[0].getSort() == theory.getBooleanSort()) {
			// Idea: if we find false:
			//       - If we additionally find true: return false
			//       - Otherwise we have to negate all other occurrences
			//       if we only find true:
			//       - conjoin all elements
			boolean foundTrue = false;
			boolean foundFalse = false;
			for (Term t : args) {
				if (t == theory.TRUE) {
					foundTrue = true;
					if (foundFalse)
						return theory.FALSE;
				} else if (t == theory.FALSE) {
					foundFalse = true;
					if (foundTrue)
						return theory.FALSE;
				} else
					tmp.add(t);
			}
			if (foundTrue)
				return createAnd(tmp.toArray(new Term[tmp.size()]));
			if (foundFalse)
				return theory.term("not",
						createOr(tmp.toArray(new Term[tmp.size()])));
			return theory.term("=", tmp.size() == args.length ? 
					args : tmp.toArray(new Term[tmp.size()]));
		} else {
			for (Term t : args)
				tmp.add(t);
		}
		// We had (= a ... a)
		if (tmp.size() == 1)
			return theory.TRUE;
		return theory.term("=", tmp.size() == args.length ? 
				args : tmp.toArray(new Term[tmp.size()]));
	}
	private Term createDistinct(Term... args) {
		Theory theory = args[0].getTheory();
		if (args[0].getSort() == theory.getBooleanSort()) {
			if (args.length > 2)
				return theory.FALSE;
			Term t0 = args[0];
			Term t1 = args[1];
			if (t0 == t1)
				return theory.FALSE;
			if (t0 == createNot(t1))
				return theory.TRUE;
			if (t0 == theory.TRUE)
				return createNot(t1);
			if (t0 == theory.FALSE)
				return t1;
			if (t1 == theory.TRUE)
				return createNot(t0);
			if (t1 == theory.FALSE)
				return t0;
			return theory.term("distinct", t0, t1);
		}
		HashSet<Term> tmp = new HashSet<Term>();
		for (Term t : args)
			if (!tmp.add(t))
				// We had (distinct a b a)
				return theory.FALSE;
		return theory.term("distinct", args);
	}
	private Term createAnd(Term... args) {
		// make this inplace
		for (int i = 0; i < args.length; ++i)
			args[i] = createNot(args[i]);
		return createNot(createOr(args));
	}
	public void convert(Term term) {
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			FunctionSymbol fsym = appTerm.getFunction();
			Term[] params = appTerm.getParameters();
			if (fsym.isLeftAssoc() && params.length > 2) {
				Theory theory = appTerm.getTheory();
				if (fsym == theory.m_And || fsym == theory.m_Or) {
					// We keep n-ary and/or
					enqueueWalker(new BuildApplicationTerm(appTerm));
					pushTerms(params);
					return;
				}
				BuildApplicationTerm dummy = new BuildApplicationTerm
						(theory.term(fsym, params[0], params[1]));
				for (int i = params.length-1; i > 0; i--) {
					enqueueWalker(dummy);
					pushTerm(params[i]);
				}
				pushTerm(params[0]);
				return;
			}
			if (fsym.isRightAssoc() && params.length > 2) {
				Theory theory = appTerm.getTheory();
				if (fsym == theory.m_Implies) {
					// We keep n-ary implies
					enqueueWalker(new BuildApplicationTerm(appTerm));
					pushTerms(params);
					return;
				}
				BuildApplicationTerm dummy = new BuildApplicationTerm
					(theory.term(fsym, params[params.length-2], 
							params[params.length-1]));
				for (int i = params.length-1; i > 0; i--)
					enqueueWalker(dummy);
				pushTerms(params);
				return;
			}
			if (fsym.isChainable() && params.length > 2 && 
					!fsym.getName().equals("=")) {
				Theory theory = appTerm.getTheory();
				BuildApplicationTerm and = new BuildApplicationTerm
						(theory.term("and", theory.TRUE, theory.TRUE));
				BuildApplicationTerm dummy = new BuildApplicationTerm
						(theory.term(fsym, params[0], params[1]));
				for (int i = params.length-1; i > 1; i--) {
					enqueueWalker(and);
					enqueueWalker(dummy);
					pushTerm(params[i]);
					pushTerm(params[i-1]);
				}
				enqueueWalker(dummy);
				pushTerm(params[1]);
				pushTerm(params[0]);
				return;
			}
		}
		super.convert(term);
	}
	
	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] args) {
		FunctionSymbol fsym = appTerm.getFunction();
		Theory theory = appTerm.getTheory();
		
		if (theory.getLogic().isIRA()
			&& fsym.getParameterCount() == 2 
			&& fsym.getParameterSort(0).getName().equals("Real") 
			&& fsym.getParameterSort(1) == fsym.getParameterSort(0)) {
			// IRA-Hack
			if (args == appTerm.getParameters())
				args = args.clone();
			for (int i = 0; i < args.length; i++) {
				if (args[i].getSort().getName().equals("Int"))
					args[i] = SMTAffineTerm.create(args[i])
						.toReal(fsym.getParameterSort(0));
			}
		}
		
		if (fsym.isIntern()) {
			if (fsym == theory.m_Not) {
				setResult(createNot(args[0]));
				return;
			}
			if (fsym == theory.m_And) {
				// Need to clone the args since createAnd is inplace
				setResult(createAnd(args.clone()));
				return;
			}
			if (fsym == theory.m_Or) {
				setResult(createOr(args));
				return;
			}
			if (fsym == theory.m_Implies) {
				Term[] tmp = new Term[args.length];
				// We move the conclusion in front (see Simplify tech report)
				for (int i = 1; i < args.length; ++i)
					tmp[i] = createNot(args[i - 1]);
				tmp[0] = args[args.length - 1];
				setResult(createOr(tmp));
				return;
			}
			if (fsym.getName().equals("=")) {
				setResult(createEq(args));
				return;
			}
			if (fsym.getName().equals("distinct")) {
				setResult(createDistinct(args));
				return;
			}
			if (fsym.getName().equals("<=")) {
				setResult(createLeq0(SMTAffineTerm.create(args[0])
						.add(SMTAffineTerm.create(Rational.MONE, args[1]))));
				return;
			}
			if (fsym.getName().equals(">=")) {
				setResult(createLeq0(SMTAffineTerm.create(args[1])
						.add(SMTAffineTerm.create(Rational.MONE, args[0]))));
				return;
			}
			if (fsym.getName().equals(">")) {
				setResult(createNot(createLeq0(SMTAffineTerm.create(args[0])
						.add(SMTAffineTerm.create(Rational.MONE, args[1])))));
				return;
			}
			if (fsym.getName().equals("<")) {
				setResult(createNot(createLeq0(SMTAffineTerm.create(args[1])
						.add(SMTAffineTerm.create(Rational.MONE, args[0])))));
				return;
			}
			if (fsym.getName().equals("+")) {
				setResult(SMTAffineTerm.create(args[0])
						.add(SMTAffineTerm.create(args[1])));
				return;
			}
			else if (fsym.getName().equals("-") && fsym.getParameterCount() == 2) {
				setResult(SMTAffineTerm.create(args[0])
						.add(SMTAffineTerm.create(Rational.MONE, args[1])));
				return;
			} 
			else if (fsym.getName().equals("*")) {
				SMTAffineTerm arg0 = SMTAffineTerm.create(args[0]);
				SMTAffineTerm arg1 = SMTAffineTerm.create(args[1]);
				if (arg0.isConstant()) {
					setResult(arg1.mul(arg0.getConstant()));
					return;
				} else if (arg1.isConstant()) {
					setResult(arg0.mul(arg1.getConstant()));
					return;
				} else {
					throw new UnsupportedOperationException("Unsupported non-linear arithmetic");
				}
			} else if (fsym.getName().equals("/")) {
				// FIXME 0 divisor
				SMTAffineTerm arg0 = SMTAffineTerm.create(args[0]);
				SMTAffineTerm arg1 = SMTAffineTerm.create(args[1]);
				if (arg1.isConstant()) {
					setResult(arg0.mul(arg1.getConstant().inverse()));
					return;
				} else {
					throw new UnsupportedOperationException("Unsupported non-linear arithmetic");
				}
			} else if (fsym.getName().equals("div") && fsym.getParameterCount() == 2) {
				SMTAffineTerm arg0 = SMTAffineTerm.create(args[0]);
				SMTAffineTerm arg1 = SMTAffineTerm.create(args[1]);
				Rational divisor = arg1.getConstant();
				if (arg1.isConstant() && divisor.isIntegral() && 
				    !divisor.equals(Rational.ZERO)) {
					// FIXME 0 divisor
					setResult(arg0.getTheory().term(fsym, arg0, arg1));
					return;
				} else {
					throw new UnsupportedOperationException("Unsupported non-linear arithmetic");
				}
			} else if (fsym.getName().equals("mod") && fsym.getParameterCount() == 2) {
				SMTAffineTerm arg0 = SMTAffineTerm.create(args[0]);
				SMTAffineTerm arg1 = SMTAffineTerm.create(args[1]);
				Rational divisor = arg1.getConstant();
				if (arg1.isConstant() && divisor.isIntegral() && 
				    !divisor.equals(Rational.ZERO)) {
					// FIXME 0 divisor
					Term div = arg0.getTheory().term(fsym, arg0, arg1);
					SMTAffineTerm mod = 
							arg0.add(SMTAffineTerm.create(Rational.MONE, div));
					setResult(mod);
					return;
				} else {
					throw new UnsupportedOperationException("Unsupported non-linear arithmetic");
				}
			} else if (fsym.getName().equals("-") && fsym.getParameterCount() == 1) {
				setResult(SMTAffineTerm.create(args[0]).negate());
				return;
			} else if (fsym.getName().equals("abs") && fsym.getParameterCount() == 1) {
				SMTAffineTerm arg = SMTAffineTerm.create(args[0]);
				SMTAffineTerm argNeg = arg.negate();
				setResult(createIte(createLeq0(argNeg), arg, argNeg));
				return;
			} else if (fsym.getName().equals("to_real") && fsym.getParameterCount() == 1) {
				setResult(SMTAffineTerm.create(args[0]).toReal(fsym.getReturnSort()));
				return;
			}
		}
		super.convertApplicationTerm(appTerm, args);
	}
}
