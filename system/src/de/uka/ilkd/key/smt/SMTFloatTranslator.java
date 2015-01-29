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

import java.math.BigInteger;

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
import de.uka.ilkd.key.ldt.DoubleLDT;

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


	//All integral types are stored in long format
	//Since they are technically unbounded (bounding should happen in KeY).
	//Arithmetic operators (for int/long) are not translated so no overflow can happen.
	//Only integral variables, literals and conversion to float is translated
	private static final SMTSort INTSORT = SMTSort.mkBV(64);

	public static final String HEAP_SORT = "Heap";
	public static final String FIELD_SORT = "Field";
	public static final String OBJECT_SORT = "Object";

	public static final String ARR_FUNCTION_NAME = "arr";

	/**
	 * Mapps some basic KeY operators to their equivalent built in operators.
	 * Initialized in initOpTable.
	 */
	private Map<Operator, SMTTermMultOp.Op> opTable;
	private Map<Operator, SMTTermUnaryOp.Op> opTableUnary;

	private Map<Operator, SMTTermFloatOp.Op> fopTable;
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

	/**
	 * Keep track of which terms were not translated
	 */
	private List<String> untranslatedMessages;

	/**
	 * The SMT sorts used in this translation. Use the String constants
	 * LOCSET_SORT, HEAP_SORT, etc. to get wanted sort.
	 */
	private Map<String, SMTSort> sorts;

	// some special KeY sorts
	private Sort floatSort;
	private Sort doubleSort;
	private Sort intSort;
	private Sort boolSort;
	private Sort heapSort;
	private Sort fieldSort;
	private Sort objectSort;

	public SMTFloatTranslator(Services services) {
		super();
		this.services = services;

		initSorts();
		initOpTable();

		functions = new HashMap<String, SMTFunction>();
		functionDefinitionOrder = new LinkedList<String>();
		untranslatedMessages = new LinkedList<String>();
	}

	/**
	 * Fills the operator table.
	 */
	private void initOpTable() {
		FloatLDT floatLDT = services.getTypeConverter().getFloatLDT();
		DoubleLDT doubleLDT = services.getTypeConverter().getDoubleLDT();
		opTable = new HashMap<Operator, SMTTermMultOp.Op>();
		opTable.put(Junctor.AND, SMTTermMultOp.Op.AND);
		opTable.put(Junctor.OR, SMTTermMultOp.Op.OR);
		opTable.put(Junctor.IMP, SMTTermMultOp.Op.IMPLIES);
		opTable.put(Equality.EQUALS, SMTTermMultOp.Op.EQUALS);
		
		//Integer comparison
		opTable.put(services.getTypeConverter().getIntegerLDT().getLessThan(),
		        SMTTermMultOp.Op.BVSLT);
		opTable.put(services.getTypeConverter().getIntegerLDT()
		        .getLessOrEquals(), SMTTermMultOp.Op.BVSLE);
		opTable.put(services.getTypeConverter().getIntegerLDT()
		        .getGreaterThan(), SMTTermMultOp.Op.BVSGT);
		opTable.put(services.getTypeConverter().getIntegerLDT()
		        .getGreaterOrEquals(), SMTTermMultOp.Op.BVSGE);


		fopTable = new HashMap<Operator, SMTTermFloatOp.Op>();
		fopTable.put(floatLDT.getLessThan(), SMTTermFloatOp.Op.FPLT);
		fopTable.put(floatLDT.getGreaterThan(), SMTTermFloatOp.Op.FPGT);
		fopTable.put(floatLDT.getLessOrEquals(), SMTTermFloatOp.Op.FPLEQ);
		fopTable.put(floatLDT.getGreaterOrEquals(), SMTTermFloatOp.Op.FPGEQ);
		fopTable.put(floatLDT.getEquals(), SMTTermFloatOp.Op.FPEQ);
		fopTable.put(floatLDT.getAddFloatIEEE(), SMTTermFloatOp.Op.FPADD);
		fopTable.put(floatLDT.getSubFloatIEEE(), SMTTermFloatOp.Op.FPSUB);
		fopTable.put(floatLDT.getMulFloatIEEE(), SMTTermFloatOp.Op.FPMUL);
		fopTable.put(floatLDT.getDivFloatIEEE(), SMTTermFloatOp.Op.FPDIV);

		fopTable.put(floatLDT.getJavaUnaryMinusFloat(), SMTTermFloatOp.Op.FPNEG);
		fopTable.put(floatLDT.getAbs(), SMTTermFloatOp.Op.FPABS);
		fopTable.put(floatLDT.getIsNaN(), SMTTermFloatOp.Op.FPISNAN);
		fopTable.put(floatLDT.getIsZero(), SMTTermFloatOp.Op.FPISZERO);
		fopTable.put(floatLDT.getIsNormal(), SMTTermFloatOp.Op.FPISNORMAL);
		fopTable.put(floatLDT.getIsSubnormal(), SMTTermFloatOp.Op.FPISSUBNORMAL);
		fopTable.put(floatLDT.getIsInfinite(), SMTTermFloatOp.Op.FPISINFINITE);
		fopTable.put(floatLDT.getIsNegative(), SMTTermFloatOp.Op.FPISNEGATIVE);
		fopTable.put(floatLDT.getIsPositive(), SMTTermFloatOp.Op.FPISPOSITIVE);
		fopTable.put(floatLDT.getCastLongToFloat(), SMTTermFloatOp.Op.CASTLONGTOFLOAT);
		fopTable.put(floatLDT.getCastFloatToLong(), SMTTermFloatOp.Op.CASTFLOATTOLONG);

		//Double predicates and operations, translated identically to float operations
		fopTable.put(doubleLDT.getLessThan(), SMTTermFloatOp.Op.FPLT);
		fopTable.put(doubleLDT.getGreaterThan(), SMTTermFloatOp.Op.FPGT);
		fopTable.put(doubleLDT.getLessOrEquals(), SMTTermFloatOp.Op.FPLEQ);
		fopTable.put(doubleLDT.getGreaterOrEquals(), SMTTermFloatOp.Op.FPGEQ);
		fopTable.put(doubleLDT.getEquals(), SMTTermFloatOp.Op.FPEQ);
		fopTable.put(doubleLDT.getAddDoubleIEEE(), SMTTermFloatOp.Op.FPADD);
		fopTable.put(doubleLDT.getSubDoubleIEEE(), SMTTermFloatOp.Op.FPSUB);
		fopTable.put(doubleLDT.getMulDoubleIEEE(), SMTTermFloatOp.Op.FPMUL);
		fopTable.put(doubleLDT.getDivDoubleIEEE(), SMTTermFloatOp.Op.FPDIV);

		fopTable.put(doubleLDT.getJavaUnaryMinusDouble(), SMTTermFloatOp.Op.FPNEG);
		fopTable.put(doubleLDT.getAbs(), SMTTermFloatOp.Op.FPABS);
		fopTable.put(doubleLDT.getIsNaN(), SMTTermFloatOp.Op.FPISNAN);
		fopTable.put(doubleLDT.getIsZero(), SMTTermFloatOp.Op.FPISZERO);
		fopTable.put(doubleLDT.getIsNormal(), SMTTermFloatOp.Op.FPISNORMAL);
		fopTable.put(doubleLDT.getIsSubnormal(), SMTTermFloatOp.Op.FPISSUBNORMAL);
		fopTable.put(doubleLDT.getIsInfinite(), SMTTermFloatOp.Op.FPISINFINITE);
		fopTable.put(doubleLDT.getIsNegative(), SMTTermFloatOp.Op.FPISNEGATIVE);
		fopTable.put(doubleLDT.getIsPositive(), SMTTermFloatOp.Op.FPISPOSITIVE);
	}

	/**
	 * Creates the select function for a certain type.
	 */
	private SMTFunction createSelectFunction(String name, SMTSort imageSort) {

		List<SMTSort> domainSorts = new LinkedList<SMTSort>();
		domainSorts.add(sorts.get(HEAP_SORT));
		domainSorts.add(sorts.get(OBJECT_SORT));
		domainSorts.add(sorts.get(FIELD_SORT));


		SMTFunction f = new SMTFunction(name, domainSorts, imageSort);

		functions.put(name, f);
		return f;
	}

	/**
	 * Creates the arr function.
	 */
	private void createArrFunction() {
		String id = ARR_FUNCTION_NAME;
		List<SMTSort> domain = new LinkedList<SMTSort>();
		domain.add(INTSORT);
		SMTSort image = sorts.get(FIELD_SORT);
		SMTFunction f = new SMTFunction(id, domain, image);
		functions.put(id, f);
	}


	/**
	 * Get special KeY sorts that we need.
	 */
	private void initSorts() {
		floatSort = services.getTypeConverter().getFloatLDT().targetSort();
		doubleSort = services.getTypeConverter().getDoubleLDT().targetSort();
		intSort = services.getTypeConverter().getIntegerLDT().targetSort();
		boolSort = services.getTypeConverter().getBooleanLDT().targetSort();

		heapSort = services.getTypeConverter().getHeapLDT().targetSort();
		fieldSort = services.getTypeConverter().getHeapLDT().getFieldSort();


		//Init unbounded SMT sorts
		sorts = new HashMap<String, SMTSort>();
		sorts.put(HEAP_SORT, new SMTSort(HEAP_SORT));
		sorts.put(OBJECT_SORT, new SMTSort(OBJECT_SORT));
		sorts.put(FIELD_SORT, new SMTSort(FIELD_SORT));
	}

	@Override
	public StringBuffer translateProblem(Term problem, Services services,
	        SMTSettings settings) throws IllegalFormulaException {
		this.settings = settings;
		this.services = services;
		SMTFile file = translateProblem(problem);
		String s = file.toString();

		//Add all comments regarding untranslated terms
		StringBuffer buffer = new StringBuffer(s);
		if (!untranslatedMessages.isEmpty()) {
			buffer.append(";==========UNTRANSLATED PARTS==========\n\n");

			for (String comment : untranslatedMessages) {
				String c2 = comment.replaceAll("\n|\r","\n;");
				buffer.append(";" + c2 + "\n");
			}
		}

		return buffer;
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

		createArrFunction();

		// Translate the proof obligation
		SMTTerm po = translateSequent(problem);
		po = po.not();
		po.setComment("The negated proof obligation");

		//Add sort declarations
		for (String s : sorts.keySet()) {
			file.addSort(sorts.get(s));
		}


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
		//by cutting off parts that can't be translated, but
		//without violating soundness
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
				untranslatedMessages.add("*Untranslated term:  " + term);
				untranslatedMessages.add("    " + e.getMessage());
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
		} else if (fopTable.containsKey(op)) {
			List<SMTTerm> subs = new LinkedList<SMTTerm>();
			for (Term t : term.subs()) {
			    subs.add(translateTerm(t));
			}

			return new SMTTermFloatOp(fopTable.get(op), subs);
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

		} else if (op == services.getTypeConverter().getFloatLDT()
		        .getFloatSymbol()) {
			Debug.assertTrue(term.arity() == 2);
			String fplitstring = NumberTranslation.translateFloatToSMTLIB(term, services);
			return new SMTTermFloatLiteral(fplitstring);

		} else if (op == services.getTypeConverter().getDoubleLDT()
		        .getDoubleSymbol()) {
			Debug.assertTrue(term.arity() == 2);
			String fplitstring = NumberTranslation.translateDoubleToSMTLIB(term, services);
			return new SMTTermFloatLiteral(fplitstring, SMTSort.DOUBLE);

		} else if (op == services.getTypeConverter().getIntegerLDT()
			.getNumberSymbol()) {
			Term number = term.sub(0);

			//Both int and long literal fit in 64 bits, and both translate the same
			BigInteger bi = NumberTranslation.translate(number);
			return new SMTTermNumber(bi.intValue(), 64, INTSORT);
		} else if (op == services.getTypeConverter().getFloatLDT()
		        .getRoundingModeRNE()) {
			return SMTTermConst.FP_RNE;
		} else if (op instanceof Function) {
			Function fun = (Function) op;
			if (isTrueConstant(fun, services)) {
				return SMTTerm.TRUE;
			} else if (isFalseConstant(fun, services)) {
				return SMTTerm.FALSE;
			} else {
				return translateCall(fun, term.subs());
			}
		} else {
			String msg = "Unable to translate " + term + " of type " +
				term.getClass().getName();
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
		} else if (s.equals(doubleSort)) {
			return SMTSort.DOUBLE;
		} else if (s.equals(intSort)) {
			return INTSORT;
		} else if (s.equals(heapSort)) {
			return sorts.get(HEAP_SORT);
		} else if (s.equals(fieldSort)) {
			return sorts.get(FIELD_SORT);
		} else {
			//Translate all object types as Object sort
			Sort obj = services.getJavaInfo().getJavaLangObject().getSort();
			if (s.equals(obj) || s.extendsTrans(obj)) {
				return sorts.get(OBJECT_SORT);
			} else {
				String msg = "Translation Failed: Unsupported Sort: " + s.name();
				throw new NoTranslationAvailableException(msg);
			}
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
		} else if (fun.sort().equals(fieldSort) && subs.isEmpty()) {
			//A field name.
			//Add a smt function declaration for the field name
			name = name.replace("$", "");
			SMTSort imageSort = translateSort(fun.sort());
			function = new SMTFunction(name, new LinkedList<SMTSort>(), imageSort);
			functions.put(name, function);

			return call(function, subs); 
		} else if (name.endsWith("::select")) {
			String selectName = Util.processName(name);
			
			SMTSort target = translateSort(fun.sort());
			SMTFunction f;
			if (functions.containsKey(selectName)) {
				f = functions.get(selectName);
			} else {
				f = createSelectFunction(selectName, target);
			}
			return call(f, subs);
		}
		String msg = "No translation for function " + name;
		throw new NoTranslationAvailableException(msg);
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
