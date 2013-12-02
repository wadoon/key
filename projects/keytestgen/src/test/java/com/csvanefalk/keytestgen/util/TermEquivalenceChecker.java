package com.csvanefalk.keytestgen.util;

import com.csvanefalk.keytestgen.util.parsers.TermParserException;
import com.csvanefalk.keytestgen.util.parsers.TermParserTools;
import de.uka.ilkd.key.logic.Term;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class TermEquivalenceChecker {

    private static TermEquivalenceChecker instance = null;

    public static TermEquivalenceChecker getInstance() {
        if (TermEquivalenceChecker.instance == null) {
            TermEquivalenceChecker.instance = new TermEquivalenceChecker();
        }
        return TermEquivalenceChecker.instance;
    }

    private TermEquivalenceChecker() {
    }

    public boolean areEquivalent(Term firstTerm, Term secondTerm) {

        // Extract the atoms
        Set<Term> atoms = new HashSet<Term>();
        extractAtoms(firstTerm, atoms);
        extractAtoms(secondTerm, atoms);

        // Create the truth table
        TruthTable truthTable = new TruthTable(atoms);

        // Test for equivalence
        for (int row = 0; row < truthTable.getRowCount(); row++) {
            Map<Term, Boolean> truthMapping = truthTable.getMapForRow(row);
            if (!compareTerms(firstTerm, secondTerm, truthMapping)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Extract all propositional atoms from the a term.
     *
     * @param term  the term
     * @param atoms the atoms
     */
    private void extractAtoms(Term term, Set<Term> atoms) {

        if (isBooleanComparator(term)) {
            atoms.add(term);
        } else {
            for (Term subTerm : term.subs()) {
                extractAtoms(subTerm, atoms);
            }
        }
    }

    /**
     * @param term a term
     * @return true if the term is a boolean comparator, false otherwise.
     */
    public static boolean isBooleanComparator(Term term) {
        return TermParserTools.isArithmeticComparator(term)
                || TermParserTools.isEquals(term);
    }

    private class TruthTable {

        Term[] atomsIndex;
        boolean[][] table;

        public TruthTable(Set<Term> atomSet) {

            Term[] atoms = new Term[atomSet.size()];
            atomSet.toArray(atoms);

            int size = (int) Math.pow(2, atoms.length);

            // Setup the atoms index according to the number of atoms
            atomsIndex = new Term[atoms.length];

            // Create the table itself
            table = new boolean[atoms.length][size];

            for (int counter = 0; counter < atoms.length; counter++) {

                Term atom = atoms[counter];

                // Add the atom to the index
                atomsIndex[counter] = atom;

                // Setup the corresponding column of truth values
                boolean[] column = new boolean[size];
                boolean truthValue = true;
                int divisor = (int) Math.pow(2, counter);
                for (int i = 1; i <= size; i++) {
                    column[i - 1] = truthValue;
                    if (i % divisor == 0) {
                        truthValue = !truthValue;
                    }
                }

                // Add the column to the table
                table[counter] = column;
            }
        }

        private Map<Term, Boolean> getMapForRow(int row) {
            Map<Term, Boolean> truthMap = new HashMap<Term, Boolean>();
            for (int column = 0; column < table.length; column++) {
                Term term = atomsIndex[column];
                Boolean value = table[column][row];
                truthMap.put(term, value);
            }
            return truthMap;
        }

        public int getRowCount() {
            return table[0].length;
        }

        public int getColumnCount() {
            return table.length;
        }
    }

    private boolean compareTerms(Term firstTerm, Term secondTerm,
                                 Map<Term, Boolean> truthMapping) {

        return evaluateTerm(firstTerm, truthMapping) == evaluateTerm(
                secondTerm, truthMapping);

    }

    protected boolean evaluateAnd(final Term term,
                                  Map<Term, Boolean> truthMapping) {

        return evaluateTerm(term.sub(0), truthMapping)
                && evaluateTerm(term.sub(1), truthMapping);
    }

    protected boolean evaluateBinaryFunction(final Term term,
                                             Map<Term, Boolean> truthMapping) {

        return truthMapping.get(term);
    }

    protected boolean evaluateBooleanConstant(final Term term,
                                              Map<Term, Boolean> truthMapping) {
        return truthMapping.get(term);
    }

    protected boolean evaluateEquals(final Term term,
                                     Map<Term, Boolean> truthMapping) {

        return evaluateTerm(term.sub(0), truthMapping) == evaluateTerm(
                term.sub(1), truthMapping);
    }

    protected boolean evaluateExistsQuantifier(final Term term,
                                               Map<Term, Boolean> truthMapping) {

        return truthMapping.get(term);
    }

    protected boolean evaluateForAllQuantifier(final Term term,
                                               Map<Term, Boolean> truthMapping) {

        return truthMapping.get(term);
    }

    protected boolean evaluateFormula(final Term term,
                                      Map<Term, Boolean> truthMapping) {

        if (TermParserTools.isObserverFunction(term)) {
            return evaluateObserverFunction(term, truthMapping);
        }
        return truthMapping.get(term);
    }

    protected boolean evaluateFunction(final Term term,
                                       Map<Term, Boolean> truthMapping) {

        if (TermParserTools.isNullSort(term)) {
            return evaluateNull(term, truthMapping);
        }

        if (TermParserTools.isSortDependingFunction(term)) {
            return evaluateSortDependentFunction(term, truthMapping);
        }

        if (TermParserTools.isBinaryFunction(term)) {
            return evaluateBinaryFunction(term, truthMapping);
        }

        if (TermParserTools.isUnaryFunction(term)) {
            return evaluateUnaryFunction(term, truthMapping);
        }

        if (TermParserTools.isLiteral(term)) {
            return evaluateLiteral(term, truthMapping);
        }

        if (TermParserTools.isProgramMethod(term)) {
            return evaluateProgramMethod(term, truthMapping);
        }

        if (TermParserTools.isFormula(term)) {
            return evaluateFormula(term, truthMapping);
        }

        try {
            if (TermParserTools.isBooleanConstant(term)) {
                return evaluateBooleanConstant(term, truthMapping);
            }
        } catch (TermParserException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        return truthMapping.get(term);
    }

    protected boolean evaluateIfExThenElse(final Term term,
                                           Map<Term, Boolean> truthMapping) {

        return truthMapping.get(term);
    }

    protected boolean evaluateIfThenElse(final Term term,
                                         Map<Term, Boolean> truthMapping) {

        return truthMapping.get(term);
    }

    protected boolean evaluateImplication(final Term term,
                                          Map<Term, Boolean> truthMapping) {

        return !evaluateTerm(term.sub(0), truthMapping)
                || evaluateTerm(term.sub(1), truthMapping);
    }

    protected boolean evaluateJunctor(final Term term,
                                      Map<Term, Boolean> truthMapping) {

        if (TermParserTools.isAnd(term)) {
            return evaluateAnd(term, truthMapping);

        } else if (TermParserTools.isOr(term)) {
            return evaluateOr(term, truthMapping);

        } else if (TermParserTools.isEquals(term)) {
            return evaluateEquals(term, truthMapping);

        } else if (TermParserTools.isNot(term)) {
            return evaluateNot(term, truthMapping);

        } else if (TermParserTools.isImplication(term)) {
            return evaluateImplication(term, truthMapping);

        } else if (TermParserTools.isFormula(term)) {
            return evaluateFormula(term, truthMapping);
        }

        return truthMapping.get(term);
    }

    protected boolean evaluateLiteral(final Term term,
                                      Map<Term, Boolean> truthMapping) {

        /*
         * Literals may or may not declare children, such as 1(#);
         */
        if (!term.subs().isEmpty()) {
            return evaluateTerm(term.sub(0), truthMapping);

        } else {
            return truthMapping.get(term);
        }
    }

    protected boolean evaluateNot(final Term term,
                                  Map<Term, Boolean> truthMapping) {

        return !evaluateTerm(term.sub(0), truthMapping);

    }

    protected boolean evaluateOr(final Term term,
                                 Map<Term, Boolean> truthMapping) {

        return evaluateTerm(term.sub(0), truthMapping)
                || evaluateTerm(term.sub(1), truthMapping);
    }

    protected boolean evaluateProgramMethod(final Term term,
                                            Map<Term, Boolean> truthMapping) {

        if (TermParserTools.isObserverFunction(term)) {
            return evaluateObserverFunction(term, truthMapping);
        }

        return truthMapping.get(term);
    }

    protected boolean evaluateProgramVariable(final Term term,
                                              Map<Term, Boolean> truthMapping) {

        if (TermParserTools.isLocationVariable(term)) {
            return evaluateLocationVariable(term, truthMapping);
        }

        return truthMapping.get(term);
    }

    protected boolean evaluateQuantifier(final Term term,
                                         Map<Term, Boolean> truthMapping) {

        if (TermParserTools.isExistsQuantifier(term)) {
            return evaluateExistsQuantifier(term, truthMapping);
        }

        if (TermParserTools.isForAllQuantifier(term)) {
            return evaluateForAllQuantifier(term, truthMapping);
        }

        return truthMapping.get(term);
    }

    protected boolean evaluateSortDependentFunction(final Term term,
                                                    Map<Term, Boolean> truthMapping) {

        return truthMapping.get(term);
    }

    protected boolean evaluateSortedOperator(final Term term,
                                             Map<Term, Boolean> truthMapping) {

        if (TermParserTools.isFunction(term)) {
            return evaluateFunction(term, truthMapping);
        }

        if (TermParserTools.isEquals(term)) {
            return evaluateEquals(term, truthMapping);
        }

        if (TermParserTools.isJunctor(term)) {
            return evaluateJunctor(term, truthMapping);
        }

        if (TermParserTools.isProgramVariable(term)) {
            return evaluateProgramVariable(term, truthMapping);
        }

        if (TermParserTools.isLogicVariable(term)) {
            return evaluateLogicVariable(term, truthMapping);
        }

        if (TermParserTools.isQuantifier(term)) {
            return evaluateQuantifier(term, truthMapping);
        }
        return truthMapping.get(term);
    }

    protected boolean evaluateTerm(final Term term,
                                   Map<Term, Boolean> truthMapping) {

        if (TermParserTools.isSortedOperator(term)) {
            return evaluateSortedOperator(term, truthMapping);

        } else if (TermParserTools.isIfExThenElse(term)) {
            return evaluateIfExThenElse(term, truthMapping);

        } else if (TermParserTools.isIfThenElse(term)) {
            return evaluateIfThenElse(term, truthMapping);
        }
        return truthMapping.get(term);
    }

    protected boolean evaluateLocationVariable(final Term term,
                                               Map<Term, Boolean> truthMapping) {

        return truthMapping.get(term);
    }

    protected boolean evaluateLogicVariable(final Term term,
                                            Map<Term, Boolean> truthMapping) {

        return truthMapping.get(term);
    }

    protected boolean evaluateNull(final Term term,
                                   Map<Term, Boolean> truthMapping) {

        return truthMapping.get(term);
    }

    protected boolean evaluateObserverFunction(final Term term,
                                               Map<Term, Boolean> truthMapping) {

        return truthMapping.get(term);
    }

    protected boolean evaluateUnaryFunction(final Term term,
                                            Map<Term, Boolean> truthMapping) {

        return evaluateTerm(term.sub(0), truthMapping);
    }
}

/*
 * 
 * protected boolean evaluateLocationVariable(final Term term, Map<Term,
 * Boolean> truthMapping) {
 * 
 * return term; }
 * 
 * protected boolean evaluateLogicVariable(final Term term, Map<Term, Boolean>
 * truthMapping) {
 * 
 * return term; }
 * 
 * protected boolean evaluateNull(final Term term, Map<Term, Boolean>
 * truthMapping) {
 * 
 * return term; }
 * 
 * protected boolean evaluateObserverFunction(final Term term, Map<Term,
 * Boolean> truthMapping) {
 * 
 * return term; }
 * 
 * protected boolean evaluateUnaryFunction(final Term term, Map<Term, Boolean>
 * truthMapping) {
 * 
 * final boolean child = evaluateTerm(term.sub(0), truthMapping);
 * 
 * final boolean newTerm = termFactory.createTerm(term.op(), child);
 * 
 * return newTerm; }
 */