package com.csvanefalk.keytestgen.keystone.simplex;

import com.csvanefalk.keytestgen.keystone.equations.Equation;
import com.csvanefalk.keytestgen.keystone.equations.EquationSystem;
import com.csvanefalk.keytestgen.keystone.equations.expression.Variable;
import org.apache.commons.math3.fraction.Fraction;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Various methods for solving constraints using the Simplex method.
 *
 * @author christopher
 */
public strictfp class Simplex {

    public static void addRows(final Fraction[][] table,
                               final int indexOfSourceRow,
                               final int indexOfTargetRow,
                               Fraction multiplier) {

        if (multiplier == null) {
            multiplier = Fraction.ONE;
        }

        for (int i = 0; i < table[indexOfSourceRow].length; i++) {
            final Fraction sourceVal = table[indexOfTargetRow][i];
            final Fraction targetVal = table[indexOfSourceRow][i].multiply(multiplier);
            table[indexOfTargetRow][i] = sourceVal.add(targetVal);
        }
    }

    private static Fraction[][] constructInitialTableaux(final Fraction[][] table) {

        /*
         * Create a new, temporary tableaux which will contain the virtual
         * function, as well as the virtual variables.
         */
        final Fraction[][] newTable = new Fraction[table.length + 1][table[0].length + table.length];

        // index of the constant part of each equation.
        final int constantIndex = table[0].length - 1;
        // the length of the new equations (i.e. old + virtual variables)
        final int equationLength = newTable[0].length;
        // index to insert the next virtual variable
        int virtualIndex = constantIndex;

        /*
         * Fill in the new tableaux, introducing the virtual objective function
         * and virtual variables as we go along.
         */
        for (int i = 1; i < newTable.length; i++) {

            final Fraction constant = table[i - 1][constantIndex];

            /*
             * Put in the regular and dummy variables
             */
            for (int j = 0; j < constantIndex; j++) {
                newTable[i][j] = table[i - 1][j];
            }

            /*
             * Put in the virtual variables
             */
            for (int k = constantIndex; k < (equationLength - 1); k++) {
                if (k == virtualIndex) {
                    newTable[i][k] = new Fraction(1);
                } else {
                    newTable[i][k] = new Fraction(0);
                }
            }
            virtualIndex++;

            /*
             * Finally, add the constant part again.
             */
            newTable[i][equationLength - 1] = constant;
        }

        /*
         * Add the virtual objective function
         */
        for (int i = 0; i < constantIndex; i++) {
            newTable[0][i] = new Fraction(0);
        }

        for (int i = constantIndex; i < (equationLength - 1); i++) {
            newTable[0][i] = new Fraction(-1);
        }

        newTable[0][equationLength - 1] = Fraction.ZERO;

        return newTable;
    }

    /**
     * Prototype solver method.
     *
     * @return
     */
    public static Map<String, Integer> experimentalSolve(final EquationSystem equationSystem) {

        final List<Equation> equations = equationSystem.getEquations();
        final Map<String, Variable> variables = equationSystem.getVariableIndex();

        /*
         * Construct the index mapping in the tableaux for the variables.
         */
        int index = 0;
        final Map<Integer, Variable> variableIndex = new HashMap<Integer, Variable>();
        for (final Variable variable : variables.values()) {
            variableIndex.put(index, variable);
            index++;
        }

        /*
         * Create the tableaux, with extra space anticipating the objective
         * function and virtual variables.
         */
        final int rows = equations.size();
        final int columns = variableIndex.size() + 1;
        final Fraction[][] tableaux = new Fraction[rows][columns];

        /*
         * Get the multiplier for each variable and insert it into the tableaux.
         */
        for (int i = 0; i < equations.size(); i++) {
            final Equation equation = equations.get(i);

            for (int j = 0; j < variableIndex.size(); j++) {
                final Variable variable = equation.getVariable(variableIndex.get(j).getName());
                if (variable != null) {
                    tableaux[i][j] = variable.resolveMultiplier();
                } else {
                    tableaux[i][j] = Fraction.ZERO;
                }
            }

            /*
             * Add the constant part of the equation.
             */
            tableaux[i][variableIndex.size()] = equation.getConstant();
        }

        /*
         * Apply Simplex to solve the system.
         */
        final Map<Variable, Fraction> solution = Simplex.solvePhaseOne(tableaux, variableIndex);

        final Map<String, Integer> finalSolution = new HashMap<String, Integer>();
        for (final Variable variable : solution.keySet()) {
            if (variable.getClass() == Variable.class) {
                final Fraction value = solution.get(variable);
                finalSolution.put(variable.getName(), value.intValue());
            }
        }

        return finalSolution;
    }

    private static Fraction getReciprocal(final Fraction fraction) {
        return new Fraction(fraction.getDenominator(), fraction.getNumerator());
    }

    private static int indexOfLargestColumnValue(final Fraction[][] table, final int rowIndex) {
        int resultIndex = -1;
        Fraction largest = Fraction.ZERO;
        for (int i = 0; i < (table[rowIndex].length - 1); i++) {
            if (table[rowIndex][i].compareTo(largest) > 0) {
                largest = table[0][i];
                resultIndex = i;
            }
        }
        return resultIndex;
    }

    private static int indexOfLargestRowValue(final Fraction[][] table, final int columnIndex) {
        int resultIndex = -1;
        Fraction largest = Fraction.ZERO;
        for (int i = 1; i < table.length; i++) {
            if (table[i][columnIndex].compareTo(largest) > 0) {
                largest = table[i][columnIndex];
                resultIndex = i;
            }
        }
        return resultIndex;
    }

    private static void multiplyRow(final Fraction[][] table, final int rowIndex, final Fraction multiplier) {

        for (int i = 0; i < table[rowIndex].length; i++) {
            table[rowIndex][i] = table[rowIndex][i].multiply(multiplier);
        }
    }

    private static Map<Variable, Fraction> solvePhaseOne(final Fraction[][] table,
                                                         final Map<Integer, Variable> variableIndex) {

        final Fraction[][] initialTableaux = Simplex.constructInitialTableaux(table);

        /*
         * Step 1: add all rows to the objective function in order to initially
         * eliminate the virtual variables.
         */
        for (int i = 1; i < initialTableaux.length; i++) {
            Simplex.addRows(initialTableaux, i, 0, null);
        }

        final Map<Integer, Integer> boundVariables = new HashMap<Integer, Integer>();

        final int objectiveSolutionIndex = initialTableaux[0].length - 1;
        while (initialTableaux[0][objectiveSolutionIndex].compareTo(Fraction.ZERO) != 0) {

            /*
             * Perform the actual minimization.
             */
            final int largestColumnIndex = Simplex.indexOfLargestColumnValue(initialTableaux, 0);
            final int largestRowIndex = Simplex.indexOfLargestRowValue(initialTableaux, largestColumnIndex);

            /*
             * Take the reciprocal of the selected value of the entering
             * variable, and use it in order to eliminate the other values.
             */
            final Fraction reciprocal = Simplex.getReciprocal(initialTableaux[largestRowIndex][largestColumnIndex]);
            Simplex.multiplyRow(initialTableaux, largestRowIndex, reciprocal);
            for (int i = 0; i < initialTableaux.length; i++) {
                if (i != largestRowIndex) {
                    final Fraction eliminationValue = initialTableaux[i][largestColumnIndex].multiply(-1);
                    Simplex.addRows(initialTableaux, largestRowIndex, i, eliminationValue);
                }
            }

            /*
             * Store the exiting variable.
             */
            boundVariables.put(largestColumnIndex, largestRowIndex);
        }

        /*
         * Configure and return the final variable bindings.
         */
        final int valueIndex = initialTableaux[0].length - 1;
        final Map<Variable, Fraction> result = new HashMap<Variable, Fraction>();
        for (final Variable variable : variableIndex.values()) {
            result.put(variable, Fraction.ZERO);
        }
        for (final Integer variableNumber : boundVariables.keySet()) {
            final Variable variable = variableIndex.get(variableNumber);
            final Fraction value = initialTableaux[boundVariables.get(variableNumber)][valueIndex];
            result.put(variable, value);
        }

        return result;
    }
}
