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

package org.key_project.common.core.parser;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.key_project.common.core.parser.KeYCommonParser.*;
import org.key_project.common.core.parser.exceptions.ProofInputException;

import junit.framework.TestCase;

/**
 * This parser tests just the grammar (i.e., syntax) it does not 
 * perform any semantic tests.
 * @author Richard Bubel
 */
public class TestTermParser extends TestCase {


    public TestTermParser(String name) {
        super(name);
    }


    private TermContext parseTerm(String inputStr) {
        // Create the lexer
        KeYCommonLexer lexer = new KeYCommonLexer(new ANTLRInputStream(inputStr));

        // Create a buffer of tokens pulled from the lexer
        CommonTokenStream tokens = new CommonTokenStream(lexer);

        // Create the parser
        KeYCommonParser parser = new KeYCommonParser(tokens);

        // Traverse the parse tree
        try {
            return parser.term();
        }
        catch (Exception e) {
            throw new ProofInputException(e.getMessage(), e);
        }
    }

    
    private FormulaContext parseFormula(String inputStr) {
        // Create the lexer
        KeYCommonLexer lexer = new KeYCommonLexer(new ANTLRInputStream(inputStr));

        // Create a buffer of tokens pulled from the lexer
        CommonTokenStream tokens = new CommonTokenStream(lexer);

        // Create the parser
        KeYCommonParser parser = new KeYCommonParser(tokens);

        // Traverse the parse tree
        try {
            return parser.formula();
        }
        catch (Exception e) {
            throw new ProofInputException(e.getMessage(), e);
        }
    }
    
    public void testParseConjunction() {
        FormulaContext result = parseFormula("A & B");
        assertTrue("Expected a conjunction", result instanceof ConjunctiveFormulaContext);
        assertEquals("A", ((ConjunctiveFormulaContext)result).formula(0).getText());
        assertEquals("B", ((ConjunctiveFormulaContext)result).formula(1).getText());
    }

    public void testParseConjunctionAssoc() {
        FormulaContext result = parseFormula("A & B & C");
        assertEquals("A&B", ((ConjunctiveFormulaContext)result).formula(0).getText());
        assertEquals("C", ((ConjunctiveFormulaContext)result).formula(1).getText());        
    }

    public void testParseConjunctionParentheses() {
        FormulaContext result = parseFormula("A & (B & C)");
        assertEquals("A", ((ConjunctiveFormulaContext)result).formula(0).getText());
        assertEquals("B&C", ((ParenthesizedFormulaContext)((ConjunctiveFormulaContext)result).formula(1)).formula().getText());        
    }

    public void testParseConjunctionDisjunctionPrecedence() {
        FormulaContext result = parseFormula("A & B | C");
        assertTrue("Disjunction should bind weaker than conjunction.", result instanceof DisjunctiveFormulaContext);
        assertEquals("A&B", ((DisjunctiveFormulaContext)result).formula(0).getText());
        assertEquals("C", ((DisjunctiveFormulaContext)result).formula(1).getText());
    }

    public void testParseConjunctionDisjunctionParenOverridesPrecedence() {
        FormulaContext result = parseFormula("A & (B | C)");
        assertEquals("A", ((ConjunctiveFormulaContext)result).formula(0).getText());
        assertEquals("(B|C)", ((ConjunctiveFormulaContext)result).formula(1).getText());
    }
    
    public void testPrecedencesProp() {
        FormulaContext result = parseFormula("A & (B | C) -> D <-> E | F");
        assertTrue("Equivalence should bind top level.", result instanceof EquivalenceFormulaContext);
        EquivalenceFormulaContext eqv = (EquivalenceFormulaContext) result;
        assertTrue("Implication on left side.", eqv.formula(0) instanceof ImplicationFormulaContext);
        assertTrue("Disjunction on right side.", eqv.formula(1) instanceof DisjunctiveFormulaContext);
    }
    
    public void testPrecedencesPropWithNeg() {
        FormulaContext result = parseFormula("!A & (B | C) -> D <-> !E | F");
        assertTrue("Equivalence should bind top level, not " + result.getClass().getSimpleName(), result instanceof EquivalenceFormulaContext);
        EquivalenceFormulaContext eqv = (EquivalenceFormulaContext) result;
        assertTrue("Implication on left side.", eqv.formula(0) instanceof ImplicationFormulaContext);
        ImplicationFormulaContext imp = (ImplicationFormulaContext)  eqv.formula(0);
        assertTrue("Conjunction !A & ...", imp.formula(0) instanceof ConjunctiveFormulaContext);
        assertTrue("Negation !A", ((ConjunctiveFormulaContext)imp.formula(0)).formula(0) instanceof NegatedFormulaContext);        
        assertTrue("Disjunction on right side.", eqv.formula(1) instanceof DisjunctiveFormulaContext);
        assertTrue("Negation !E.", ((DisjunctiveFormulaContext)eqv.formula(1)).formula(0) instanceof NegatedFormulaContext);
    }
    
    public void testComparison() {
        FormulaContext result = parseFormula("a <= b");
        assertTrue(result instanceof ComparisonFormulaContext);
        assertEquals(KeYCommonLexer.LESSEQUAL, ((ComparisonFormulaContext)result).op.getType());
        result = parseFormula("a < b");
        assertTrue(result instanceof ComparisonFormulaContext);
        assertEquals(KeYCommonLexer.LESS, ((ComparisonFormulaContext)result).op.getType());
        result = parseFormula("a > b");
        assertTrue(result instanceof ComparisonFormulaContext);
        assertEquals(KeYCommonLexer.GREATER, ((ComparisonFormulaContext)result).op.getType());
        result = parseFormula("a >= b");
        assertTrue(result instanceof ComparisonFormulaContext);
        assertEquals(KeYCommonLexer.GREATEREQUAL, ((ComparisonFormulaContext)result).op.getType());
        result = parseFormula("a = b");
        assertTrue(result instanceof ComparisonFormulaContext);
        assertEquals(KeYCommonLexer.EQUALS, ((ComparisonFormulaContext)result).op.getType());
        result = parseFormula("a != b");
        assertTrue(result instanceof ComparisonFormulaContext);
        assertEquals(KeYCommonLexer.NOT_EQUALS, ((ComparisonFormulaContext)result).op.getType());
    }
    
    public void testComparisonPrecedence() {
        FormulaContext result = parseFormula("a <= b & C");
        assertTrue(result instanceof ConjunctiveFormulaContext);
        result = parseFormula("C & a <= b | D");
        assertTrue(result instanceof DisjunctiveFormulaContext);
        assertTrue(((DisjunctiveFormulaContext)result).formula(0) instanceof ConjunctiveFormulaContext);
        assertTrue(((ConjunctiveFormulaContext)((DisjunctiveFormulaContext)result).formula(0)).formula(1) instanceof ComparisonFormulaContext);
    }
    
    
    public void testPredicateFormula() {
        FormulaContext result = parseFormula("p(a,b)");
        assertTrue(result instanceof PredicateFormulaContext);
        PredicateFormulaContext pred = (PredicateFormulaContext) result;
        assertEquals("p", pred.sym.getText());
        assertEquals(2, pred.arguments().argumentList().term().size());
    }
    
    public void testQuantifiedFormula() {
        FormulaContext result = parseFormula("\\forall x:int; A & B");

        assertTrue(result instanceof ConjunctiveFormulaContext);
        QuantifiedFormulaContext qf = (QuantifiedFormulaContext) ((ConjunctiveFormulaContext)result).formula(0);
        assertEquals(KeYCommonLexer.FORALL, qf.quantifier.getType());
        assertTrue(qf.formula() instanceof PredicateFormulaContext);
    }

    public void testFunctionTerm() {
        TermContext result = parseTerm("f(a,b)");
        assertTrue(result instanceof FunctionTermContext);
        assert(result instanceof FunctionTermContext);
        FunctionTermContext func = (FunctionTermContext) result;
        assertEquals("f", func.sym.getText());
        assertEquals(2, func.arguments().argumentList().term().size());
    }

    
}
        