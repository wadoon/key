package de.uka.ilkd.key.pp;

import java.io.IOException;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.pp.Layouter;
import de.uka.ilkd.keyabs.pp.LogicPrinter;

public interface ILogicPrinter {

	/**
	 * @return the notationInfo associated with this LogicPrinter
	 */
	public abstract INotationInfo getNotationInfo();

	/**
	 * Resets the Backend, the Layouter and (if applicable) the ProgramPrinter
	 * of this Object.
	 */
	public abstract void reset();

	/**
	 * sets the line width to the new value but does <em>not</em>
	 *  reprint the sequent.
	 * The actual set line width is the maximum of
	 *   {@link LogicPrinter#DEFAULT_LINE_WIDTH} and the given value
	 * @param lineWidth the max. number of character to put on one line
	 * @return the actual set line width
	 */
	public abstract int setLineWidth(int lineWidth);

	/** Reprints the sequent.  This can be useful if settings like
	 * PresentationFeatures or abbreviations have changed.
	 * @param seq The Sequent to be reprinted
	 * @param filter The SequentPrintFilter for seq
	 * @param lineWidth the max. number of character to put on one line
	 *   (the actual taken linewidth is the max of
	 *   {@link LogicPrinter#DEFAULT_LINE_WIDTH} and the given value
	 */
	public abstract void update(Sequent seq, SequentPrintFilter filter,
			int lineWidth);

	/**
	 * sets instantiations of schema variables
	 */
	public abstract void setInstantiation(SVInstantiations instantiations);

	/**
	 * Pretty-print a taclet. Line-breaks are taken care of.
	 *
	 * @param taclet
	 *           The Taclet to be pretty-printed.
	 * @param sv
	 *           The instantiations of the SchemaVariables
	 * @param showWholeTaclet
	 *           Should the find, varcond and heuristic part be pretty-printed?
	 * @param declareSchemaVars
	 *           Should declarations for the schema variables used in the taclet be pretty-printed?
	 */
	public abstract void printTaclet(Taclet taclet, SVInstantiations sv,
			boolean showWholeTaclet, boolean declareSchemaVars);

	/**
	 * Pretty-print a taclet. Line-breaks are taken care of. No instantiation is
	 * applied.
	 *
	 * @param taclet
	 *           The Taclet to be pretty-printed.
	 */
	public abstract void printTaclet(Taclet taclet);

	/**
	 * Pretty-prints a ProgramElement.
	 *
	 * @param pe
	 *           You've guessed it, the ProgramElement to be pretty-printed
	 * @throws IOException
	 */
	public abstract void printProgramElement(ProgramElement pe)
			throws IOException;

	/**
	 * Pretty-Prints a ProgramVariable in the logic, not in Java blocks. Prints
	 * out the full (logic) name, so if A.b is private, it becomes a.A::b .
	 *
	 * @param pv
	 *           The ProgramVariable in the logic
	 * @throws IOException
	 */
	public abstract void printProgramVariable(ProgramVariable pv)
			throws IOException;

	/**
	 * Pretty-prints a ProgramSV.
	 *
	 * @param pe
	 *           You've guessed it, the ProgramSV to be pretty-printed
	 * @throws IOException
	 */
	public abstract void printProgramSV(ProgramSV pe) throws IOException;

	/**
	 * Pretty-print a sequent.
	 * The sequent arrow is rendered as <code>==&gt;</code>.  If the
	 * sequent doesn't fit in one line, a line break is inserted after each
	 * formula, the sequent arrow is on a line of its own, and formulae
	 * are indented w.r.t. the arrow.
	 * @param seq The Sequent to be pretty-printed
	 * @param filter The SequentPrintFilter for seq
	 * @param finalbreak Print an additional line-break at the end of the sequent.
	 */
	public abstract void printSequent(Sequent seq, SequentPrintFilter filter,
			boolean finalbreak);

	public abstract void printSequent(SequentPrintFilter filter,
			boolean finalbreak);

	public abstract void printSequent(Sequent seq, boolean finalbreak);

	/**
	 * Pretty-print a sequent.
	 * The sequent arrow is rendered as <code>=&gt;</code>.  If the
	 * sequent doesn't fit in one line, a line break is inserted after each
	 * formula, the sequent arrow is on a line of its own, and formulae
	 * are indented w.r.t. the arrow.
	 * A line-break is printed after the Sequent.
	 * @param seq The Sequent to be pretty-printed
	 * @param filter The SequentPrintFilter for seq
	 */
	public abstract void printSequent(Sequent seq, SequentPrintFilter filter);

	/**
	 * Pretty-print a sequent.
	 * The sequent arrow is rendered as <code>=&gt;</code>.  If the
	 * sequent doesn't fit in one line, a line break is inserted after each
	 * formula, the sequent arrow is on a line of its own, and formulae
	 * are indented w.r.t. the arrow.
	 * A line-break is printed after the Sequent.
	 * No filtering is done.
	 * @param seq The Sequent to be pretty-printed
	 */
	public abstract void printSequent(Sequent seq);

	/**
	 * Pretty-prints a Semisequent.  Formulae are separated by commas.
	 *
	 * @param semiseq the semisequent to be printed
	 */
	public abstract void printSemisequent(Semisequent semiseq)
			throws IOException;

	public abstract void printSemisequent(
			ImmutableList<SequentPrintFilterEntry> p_formulas)
			throws IOException;

	/**
	 * Pretty-prints a constrained formula. The constraint
	 * "Constraint.BOTTOM" is suppressed
	 *
	 * @param cfma the constrained formula to be printed
	 */
	public abstract void printConstrainedFormula(SequentFormula cfma)
			throws IOException;

	/**
	 * Pretty-prints a term or formula.  How it is rendered depends on
	 * the NotationInfo given to the constructor.
	 *
	 * @param t the Term to be printed
	 */
	public abstract void printTerm(Term t) throws IOException;

	/**
	 * Pretty-prints a set of terms.
	 * @param terms the terms to be printed
	 */
	public abstract void printTerm(ImmutableSet<Term> terms) throws IOException;

	/**
	 * Pretty-prints a term or formula in the same block.  How it is
	 * rendered depends on the NotationInfo given to the constructor.
	 * `In the same block' means that no extra indentation will be
	 * added if line breaks are necessary.  A formula <code>a &amp; (b
	 * &amp; c)</code> would print <code>a &amp; b &amp; c</code>, omitting
	 * the redundant parentheses.  The subformula <code>b &amp; c</code>
	 * is printed using this method to get a layout of
	 *
	 * <pre>
	 *   a
	 * &amp; b
	 * &amp; c
	 * </pre>
	 * instead of
	 * <pre>
	 *   a
	 * &amp;   b
	 *   &amp; c
	 * </pre>
	 *
	 *
	 * @param t the Term to be printed */
	public abstract void printTermContinuingBlock(Term t) throws IOException;

	/** Print a term in <code>f(t1,...tn)</code> style.  If the
	 * operator has arity 0, no parentheses are printed, i.e.
	 * <code>f</code> instead of <code>f()</code>.  If the term
	 * doesn't fit on one line, <code>t2...tn</code> are aligned below
	 * <code>t1</code>.
	 *
	 * @param name the name to be printed before the parentheses.
	 * @param t the term to be printed.  */
	public abstract void printFunctionTerm(String name, Term t)
			throws IOException;

	public abstract void printCast(String pre, String post, Term t, int ass)
			throws IOException;

	public abstract void printSelect(Term t) throws IOException;

	public abstract void printLength(Term t) throws IOException;

	public abstract void printObserver(Term t) throws IOException;

	public abstract void printSingleton(Term t) throws IOException;

	public abstract void printElementOf(Term t) throws IOException;

	public abstract void printElementOf(Term t, String symbol)
			throws IOException;

	/** Print a unary term in prefix style.  For instance
	 * <code>!a</code>.  No line breaks are possible.
	 *
	 * @param name the prefix operator
	 * @param t    the subterm to be printed
	 * @param ass  the associativity for the subterm
	 */
	public abstract void printPrefixTerm(String name, Term t, int ass)
			throws IOException;

	/** Print a unary term in postfix style.  For instance
	 * <code>t.a</code>, where <code>.a</code> is the postfix operator.
	 * No line breaks are possible.
	 *
	 * @param name the postfix operator
	 * @param t    the subterm to be printed
	 * @param ass  the associativity for the subterm
	 */
	public abstract void printPostfixTerm(Term t, int ass, String name)
			throws IOException;

	/** Print a binary term in infix style.  For instance <code>p
	 * &amp; q</code>, where <code>&amp;</code> is the infix
	 * operator.  If line breaks are necessary, the format is like
	 *
	 * <pre>
	 *   p
	 * & q
	 * </pre>
	 *
	 * The subterms are printed using
	 * {@link #printTermContinuingBlock(Term)}.
	 *
	 * @param l    the left subterm
	 * @param assLeft associativity for left subterm
	 * @param name the infix operator
	 * @param r    the right subterm
	 * @param assRight associativity for right subterm
	 */
	public abstract void printInfixTerm(Term l, int assLeft, String name,
			Term r, int assRight) throws IOException;

	/** Print a binary term in infix style, continuing a containing
	 * block.  See {@link #printTermContinuingBlock(Term)} for the
	 * idea.  Otherwise like
	 * {@link #printInfixTerm(Term,int,String,Term,int)}.
	 *
	 * @param l    the left subterm
	 * @param assLeft associativity for left subterm
	 * @param name the infix operator
	 * @param r    the right subterm
	 * @param assRight associativity for right subterm
	 * */
	public abstract void printInfixTermContinuingBlock(Term l, int assLeft,
			String name, Term r, int assRight) throws IOException;

	/**
	 * Print a term with an update. This looks like
	 * <code>{u} t</code>.  If line breaks are necessary, the
	 * format is
	 *
	 * <pre>
	 * {u}
	 *   t
	 * </pre>
	 *
	 * @param l       the left brace
	 * @param r       the right brace
	 * @param t       the update term
	 * @param ass3    associativity for phi
	 */
	public abstract void printUpdateApplicationTerm(String l, String r, Term t,
			int ass3) throws IOException;

	/**
	 * Print an elementary update.  This looks like
	 * <code>loc := val</code>
	 *
	 * @param asgn    the assignment operator (including spaces)
	 * @param ass2    associativity for the new values
	 */
	public abstract void printElementaryUpdate(String asgn, Term t, int ass2)
			throws IOException;

	public abstract void printParallelUpdate(String separator, Term t, int ass)
			throws IOException;

	public abstract void printIfThenElseTerm(Term t, String keyword)
			throws IOException;

	/** Print a substitution term.  This looks like
	 * <code>{var/t}s</code>.  If line breaks are necessary, the
	 * format is
	 *
	 * <pre>
	 * {var/t}
	 *   s
	 * </pre>
	 *
	 * @param l       the String used as left brace symbol
	 * @param v       the {@link QuantifiableVariable} to be substituted
	 * @param t       the Term to be used as new value 
	 * @param ass2    the int defining the associativity for the new value
	 * @param r       the String used as right brace symbol
	 * @param phi     the substituted term/formula
	 * @param ass3    the int defining the associativity for phi
	 */
	public abstract void printSubstTerm(String l, QuantifiableVariable v,
			Term t, int ass2, String r, Term phi, int ass3) throws IOException;

	/** Print a quantified term.  Normally, this looks like
	 * <code>all x:s.phi</code>.  If line breaks are necessary,
	 * the format is
	 *
	 * <pre>
	 * all x:s.
	 *   phi
	 * </pre>
	 *
	 * Note that the parameter <code>var</code> has to contain the
	 * variable name with colon and sort.
	 *
	 * @param name the name of the quantifier
	 * @param vars  the quantified variables (+colon and sort)
	 * @param phi  the quantified formula
	 * @param ass  associativity for phi
	 */
	public abstract void printQuantifierTerm(String name,
			ImmutableArray<QuantifiableVariable> vars, Term phi, int ass)
			throws IOException;

	/** Print a constant.  This just prints the string <code>s</code> and
	 * marks it as a nullary term.
	 *
	 * @param s the constant
	 */
	public abstract void printConstant(String s) throws IOException;

	/**
	 * Print a Java block.  This is formatted using the ProgramPrinter
	 * given to the constructor.  The result is indented according to
	 * the surrounding material.  The first `executable' statement is
	 * marked for highlighting.
	 *
	 * @param j the Java block to be printed
	 */
	public abstract void printJavaBlock(JavaBlock j) throws IOException;

	/** Print a DL modality formula.  <code>phi</code> is the whole
	 * modality formula, not just the subformula inside the modality.
	 * Normally, this looks like
	 * <code>&lt;Program&gt;psi</code>, where <code>psi = phi.sub(0)</code>.
	 * No line breaks are inserted, as the program itself is always broken.
	 * In case of a program modality with arity greater than 1,
	 * the subformulae are listed between parens, like
	 * <code>&lt;Program&gt;(psi1,psi2)</code>
	 */

	public abstract void printModalityTerm(String left, JavaBlock jb,
			String right, Term phi, int ass) throws IOException;

	/**
	 * Returns the pretty-printed sequent.  This should only be called
	 * after a <tt>printSequent</tt> invocation returns.
	 *
	 * @return the pretty-printed sequent.
	 */
	public abstract String toString();

	/**
	 * Returns the pretty-printed sequent in a StringBuffer.  This
	 * should only be called after a <tt>printSequent</tt> invocation
	 * returns.
	 *
	 * @return the pretty-printed sequent.  
	 */
	public abstract StringBuffer result();

	/**
	 * returns the PositionTable representing position information on
	 * the sequent of this LogicPrinter. Subclasses may overwrite
	 * this method with a null returning body if position information
	 * is not computed there.
	 */
	public abstract InitialPositionTable getPositionTable();

	/** Returns the ProgramPrinter
	 * @return the ProgramPrinter
	 */
	public abstract ProgramPrinter programPrinter();

	/**
	 * @return The SVInstantiations given with the last printTaclet call.
	 */
	public abstract SVInstantiations getInstantiations();

	/**
	 * returns true if an attribute term shall be printed in short form.
	 * In opposite to the other <tt>printInShortForm</tt> methods
	 * it takes care of meta variable instantiations
	 * @param attributeProgramName the String of the attribute's program
	 * name
	 * @param t the Term used as reference prefix
	 * @return true if an attribute term shall be printed in short form.
	 */
	public abstract boolean printInShortForm(String attributeProgramName, Term t);

	/**
	 * tests if the program name together with the prefix sort
	 * determines the attribute in a unique way
	 * @param programName the String denoting the program name of
	 * the attribute
	 * @param sort the ObjectSort in whose reachable hierarchy
	 * we test for uniqueness
	 * @return true if the attribute is uniquely determined
	 */
	public abstract boolean printInShortForm(String programName, Sort sort);

	public abstract Layouter getLayouter();

}