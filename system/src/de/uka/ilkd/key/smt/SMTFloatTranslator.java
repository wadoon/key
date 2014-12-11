// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.smt;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.FloatLDT;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.lang.*;

import de.uka.ilkd.key.testgen.ProofInfo;
import de.uka.ilkd.key.util.Debug;

public class SMTFloatTranslator implements SMTTranslator {

  
	private static class NoTranslationAvailableException
		      extends Exception {
		public NoTranslationAvailableException(String message) {
			super(message);
		}
	}


	/**
	 * Mapps some basic KeY operators to their equivalent built in operators.
	 * Initialized in initOpTable.
	 */
	private Map<Operator, SMTTermMultOp.Op> opTable;
	private int varNr;
	/**
	 * The SMT translation settings.
	 */
	private SMTSettings settings;
	/**
	 * KeY services provide a lot of useful stuff.
	 */
	private Services services;
	/**
	 * The functions that we declare are stored here.
	 */
	private Map<String, SMTFunction> functions;
	/**
	 * Stores the order in which the function definitions should be written in
	 * the SMT file. If the id of f1 appears before the id of f2 in this list,
	 * f1 will be written before f2.
	 */
	private List<String> functionDefinitionOrder;


	// some special KeY sorts
	private Sort floatSort;
	private Sort boolSort;

	public SMTFloatTranslator(Services services) {
		super();
		this.services = services;

		initSorts();
		initOpTable();

		functions = new HashMap<String, SMTFunction>();
		functionDefinitionOrder = new LinkedList<String>();
	}

	/**
	 * Fills the operator table.
	 */
	private void initOpTable() {
		FloatLDT floatLDT = services.getTypeConverter().getFloatLDT();
		opTable = new HashMap<Operator, SMTTermMultOp.Op>();
		opTable.put(Junctor.AND, SMTTermMultOp.Op.AND);
		opTable.put(Junctor.OR, SMTTermMultOp.Op.OR);
		opTable.put(Junctor.IMP, SMTTermMultOp.Op.IMPLIES);

		opTable.put(floatLDT.getLessThan(), SMTTermMultOp.Op.FPLT);
		opTable.put(floatLDT.getGreaterThan(), SMTTermMultOp.Op.FPGT);
		opTable.put(floatLDT.getLessOrEquals(), SMTTermMultOp.Op.FPLEQ);
		opTable.put(floatLDT.getGreaterOrEquals(), SMTTermMultOp.Op.FPGEQ);
		opTable.put(floatLDT.getAddFloatIEEE(), SMTTermMultOp.Op.FPADD);
		opTable.put(floatLDT.getSubFloatIEEE(), SMTTermMultOp.Op.FPSUB);
		opTable.put(floatLDT.getMulFloatIEEE(), SMTTermMultOp.Op.FPMUL);
		opTable.put(floatLDT.getDivFloatIEEE(), SMTTermMultOp.Op.FPDIV);

		//TODO: keep table for unary ops?
	}

	/**
	 * Get special KeY sorts that we need.
	 */
	private void initSorts() {
		floatSort = services.getTypeConverter().getFloatLDT().targetSort();
		boolSort = services.getTypeConverter().getBooleanLDT().targetSort();
	}

	@Override
	public StringBuffer translateProblem(Term problem, Services services,
	        SMTSettings settings) throws IllegalFormulaException {
		this.settings = settings;
		this.services = services;
		SMTFile file = translateProblem(problem);
		String s = file.toString();
		return new StringBuffer(s);
	}

	/**
	 * Translates a KeY problem into a SMTFile.
	 * 
	 * @param problem
	 *            The KeY proof obligation.
	 * @return
	 */
	public SMTFile translateProblem(Term problem) {
		SMTFile file = new SMTFile();

		// Translate the proof obligation
		SMTTerm po = translateSequent(problem);
		po = po.not();
		po.setComment("The negated proof obligation");

		// Add other function declarations to file.
		for (String s : functions.keySet()) {
			SMTFunction f = functions.get(s);
			if (!(f instanceof SMTFunctionDef)) {
				file.addFunction(functions.get(s));
			}
		}
		// Add function definitions to file.
		for (String s : functionDefinitionOrder) {
			file.addFunction(functions.get(s));
		}
		// Add the proof obligation to file.
		file.addFormula(po);
		return file;
	}

	/**
	 * Translates a sequent
	 *
	 * @param sequent
	 *	      The sequent
	 *
	 * @return the SMTTerm which is the translation of the sequent
	 */
	public SMTTerm translateSequent(Term sequent) {
		//In order to preserve soundness, the sequent
		//defaults to FALSE if translation fails
		return translateFormulaWithDefaultValue(sequent, SMTTerm.FALSE);
	}

	/**
	 * Translates a KeY formula into an SMT formula.
	 * If the translation fails, the result will be
	 * logically equivalent to the provided default value
	 * 
	 * @param term
	 *            the KeY term, which should be a formula.
	 * @param defaultValue
	 *	      the default value
	 * @return the SMT term.
	 */
	public SMTTerm translateFormulaWithDefaultValue(Term term, SMTTerm defaultValue) {
		Operator op = term.op();

		//The default value is used to partially translate a sequent
		//by cutting off parts that can't be translated, but without
		//violating soundness
		if (op == Junctor.NOT) {
			SMTTerm sub = translateFormulaWithDefaultValue(
				term.sub(0), defaultValue.not());
			return sub.not();
		} else if (op == Junctor.AND) {
			SMTTerm t1 = translateFormulaWithDefaultValue(term.sub(0), defaultValue);
			SMTTerm t2 = translateFormulaWithDefaultValue(term.sub(1), defaultValue);
			return t1.and(t2);
		} else if (op == Junctor.OR) {
			SMTTerm t1 = translateFormulaWithDefaultValue(term.sub(0), defaultValue);
			SMTTerm t2 = translateFormulaWithDefaultValue(term.sub(1), defaultValue);
			return t1.or(t2);
		} else if (op == Junctor.IMP) {
			SMTTerm t1 = translateFormulaWithDefaultValue(term.sub(0), defaultValue.not());
			SMTTerm t2 = translateFormulaWithDefaultValue(term.sub(1), defaultValue);
			return t1.implies(t2);
		} else {
			try {
				return translateTerm(term);
			} catch (NoTranslationAvailableException e) {
				return defaultValue;
			}
		}
	}

	/**
	 * Translates a KeY term to an SMT term.
	 * 
	 * @param term
	 *            the KeY term.
	 * @return the SMT term.
	 */
	public SMTTerm translateTerm(Term term)
	    throws NoTranslationAvailableException {
		Operator op = term.op();
		if (opTable.containsKey(op)) {

			List<SMTTerm> args = new LinkedList<SMTTerm>();
			for (Term t : term.subs()) {
			    args.add(translateTerm(t));
			}
			return new SMTTermMultOp(opTable.get(op), args);
		} else if (op == Junctor.NOT) {
			SMTTerm sub = translateTerm(term.sub(0));
			return sub.not();
		} else if (op == IfThenElse.IF_THEN_ELSE) {
			SMTTerm condition = translateTerm(term.sub(0));
			SMTTerm trueCase = translateTerm(term.sub(1));
			SMTTerm falseCase = translateTerm(term.sub(2));
			return SMTTerm.ite(condition, trueCase, falseCase);
		} else if (op == Junctor.TRUE) {
			return SMTTerm.TRUE;
		} else if (op == Junctor.FALSE) {
			return SMTTerm.FALSE;
		} else if (op instanceof ProgramVariable) {
			ProgramVariable pv = (ProgramVariable) op;
			SMTFunction constant = translateConstant(pv.name().toString(),
			        pv.sort());
			return SMTTerm.call(constant);

		//TODO: add an "opTable" for the following unary ops?
		} else if (op == services.getTypeConverter().getFloatLDT()
		        .getFloatSymbol()) {
			Debug.assertTrue(term.arity() == 2);
			String fplitstring = NumberTranslation.translateFloatToSMTLIB(term, services);
			return new SMTTermFloatLiteral(fplitstring);
		} else if (op == services.getTypeConverter().getFloatLDT()
		        .getRoundingModeRNE()) {
			return SMTTermConst.FP_RNE;
		} else if (op instanceof Function) {
			Function fun = (Function) op;
			if (isTrueConstant(fun, services)) {
				return SMTTerm.TRUE;
			} else if (isFalseConstant(fun, services)) {
				return SMTTerm.FALSE;
			} else if (fun == services.getTypeConverter().getFloatLDT()
			        .getJavaUnaryMinusFloat()) {
			    SMTTerm subterm = translateTerm(term.sub(0));
			    return new SMTTermUnaryOp(SMTTermUnaryOp.Op.FPNEG, subterm);
			} else if (fun == services.getTypeConverter().getFloatLDT()
			        .getIsNormal()) {
			    SMTTerm subterm = translateTerm(term.sub(0));
			    return new SMTTermUnaryOp(SMTTermUnaryOp.Op.FPISNORMAL, subterm);
			} else {
				return translateCall(fun, term.subs());
			}
		} else {
			String msg = "Unable to translate " + term + " of type " +
				term.getClass().getName();
			System.err.println(msg);
			throw new NoTranslationAvailableException(msg);
		}
	}

	/**
	 * Translates a KeY sort to an SMT sort.
	 * 
	 * @param s
	 * @return
	 */
	private SMTSort translateSort(Sort s)
			throws NoTranslationAvailableException {
		if (s.equals(boolSort)) {
			return SMTSort.BOOL;
		} else if (s.equals(Sort.FORMULA)) {
			return SMTSort.BOOL;
		} else if (s.equals(floatSort)) {
			return SMTSort.FLOAT;
		} else {
			String msg = "Translation Failed: Unsupported Sort: " + s.name();
			System.err.println(msg);
			throw new NoTranslationAvailableException(msg);
		}
	}

	/**
	 * Creates an SMT constant with the specified id and sort.
	 * 
	 * @param id
	 * @param s
	 * @return
	 */
	private SMTFunction translateConstant(String id, Sort s)
			throws NoTranslationAvailableException {
		if (functions.containsKey(id)) {
			return functions.get(id);
		}
		SMTSort imageSort = translateSort(s);
		List<SMTSort> domainSorts = new LinkedList<SMTSort>();
		SMTFunction fun = new SMTFunction(id, domainSorts, imageSort);
		functions.put(id, fun);

		return fun;
	}

	/**
	 * Translates a function call of function f with argument subs.
	 * 
	 * @param fun
	 * @param subs
	 * @return
	 */
	private SMTTerm translateCall(Function fun, ImmutableArray<Term> subs)
			throws NoTranslationAvailableException {
		String name = fun.name().toString();

		SMTFunction function = null;
		if (functions.containsKey(name)) {
			function = functions.get(name);
			return call(function, subs);
		} else {
			String msg = "No translation for function " + name;
			System.err.println(msg);
			throw new NoTranslationAvailableException(msg);
		}
	}


	/**
	 * Creates an SMTTermCall using the given function and arguments.
	 * 
	 * @param function
	 * @param subs
	 * @return
	 */
	private SMTTerm call(SMTFunction function, ImmutableArray<Term> subs)
			throws NoTranslationAvailableException {
		List<SMTTerm> subTerms = new LinkedList<SMTTerm>();
		int i = 0;
		for (Term t : subs) {
			SMTTerm sub = translateTerm(t);
			SMTSort target = function.getDomainSorts().get(i);
			subTerms.add(sub);
			i++;
		}
		return SMTTerm.call(function, subTerms);
	}

	private boolean isTrueConstant(Operator o, Services s) {
		return o.equals(s.getTypeConverter().getBooleanLDT().getTrueConst());
	}

	private boolean isFalseConstant(Operator o, Services s) {
		return o.equals(s.getTypeConverter().getBooleanLDT().getFalseConst());
	}

	@Override
	public Collection<Throwable> getExceptionsOfTacletTranslation() {
		return new LinkedList<Throwable>();
	}

}
