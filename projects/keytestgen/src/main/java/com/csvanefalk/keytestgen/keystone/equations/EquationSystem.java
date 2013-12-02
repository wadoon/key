package com.csvanefalk.keytestgen.keystone.equations;

import com.csvanefalk.keytestgen.keystone.KeYStoneException;
import com.csvanefalk.keytestgen.keystone.equations.expression.DummyVariable;
import com.csvanefalk.keytestgen.keystone.equations.expression.NumericConstant;
import com.csvanefalk.keytestgen.keystone.equations.expression.Variable;
import com.csvanefalk.keytestgen.keystone.equations.restriction.IRestriction;
import com.csvanefalk.keytestgen.keystone.simplex.Simplex;
import de.uka.ilkd.key.logic.Term;
import org.apache.commons.math3.fraction.Fraction;

import javax.naming.OperationNotSupportedException;
import java.util.*;

/**
 * Instances of this class represent a system of equations.
 *
 * @author christopher
 */
public class EquationSystem {

    /**
     * Constructs a system of equations from a set of term representing either
     * equations or inequalities. All inequalities are converted by introducing
     * slack/surplus variables.
     *
     * @param terms
     * @return
     * @throws KeYStoneException
     */
    public static EquationSystem createEquationSystem(
            final Collection<Term> terms) throws KeYStoneException {

        /*
         * Create the equations
         */
        final List<Equation> equations = new ArrayList<Equation>();
        for (final Term term : terms) {

            /*
             * Convert the Term to an inequality.
             */
            final IComparator relation = EquationUtils.constructRelation(term);

            /*
             * Convert the inequality to an equation.
             */
            final Equation equation = Equation.createEquation(relation);

            equations.add(equation);
        }

        /*
         * Construct the variable index for the system.
         */
        final Map<String, Variable> variableIndex = new HashMap<String, Variable>();
        for (final Equation equation : equations) {
            variableIndex.putAll(equation.getVariables());
        }
        return new EquationSystem(equations, variableIndex);
    }

    /**
     * The equations present in the system.
     */
    List<Equation> equations = null;

    /**
     * Auxiliary restrictions on the system, imposed by KeYStone and evaluated
     * separately.
     */
    Map<Variable, List<IRestriction>> restrictions = null;

    /**
     * An index of the variables present in the system.
     */
    Map<String, Variable> variableIndex = null;

    private EquationSystem(final List<Equation> equations,
                           final Map<String, Variable> variableIndex2) {
        super();
        this.equations = equations;
        variableIndex = variableIndex2;
    }

    private boolean __debug_AssertCorrectness(
            final Map<String, Fraction> valueMapping)
            throws OperationNotSupportedException {
        resetAllVariables();

        for (final String setVariableIdentifier : valueMapping.keySet()) {
            final Variable variableToBind = variableIndex.get(setVariableIdentifier);
            final NumericConstant valueToBind = new NumericConstant(
                    valueMapping.get(variableToBind));
            variableToBind.bind(valueToBind);
        }

        for (final Equation equation : equations) {
            if (!equation.evaluate()) {
                return false;
            }
        }

        return true;
    }

    /**
     * @param equation
     * @param variableToSolve
     * @return true if the equation contains the variable, false otherwise.
     *         Reference based comparisons are enforced.
     */
    private boolean constainsVariable(final Equation equation,
                                      final Variable variableToSolve) {

        for (final Variable variable : equation.getVariables().values()) {
            if (variable == variableToSolve) {
                return true;
            }
        }
        return false;
    }

    /**
     * Prototype solver method.
     *
     * @return
     */
    public Map<String, Integer> experimentalSolve() {

        // if (equations.size() == 1) {
        // return solveSingleEquation();
        // }

        return Simplex.experimentalSolve(this);
    }

    public List<Equation> getEquations() {
        return equations;
    }

    public Map<String, Variable> getVariableIndex() {
        return variableIndex;
    }

    private void resetAllVariables() {
        for (final Variable variable : variableIndex.values()) {
            variable.bind(null);
        }
    }

    public Map<String, Fraction> solveSystem()
            throws OperationNotSupportedException, KeYStoneException {

        /*
         * Empty systems should not occur, but we accomodate them just in case.
         */
        if (equations.isEmpty()) {
            return new HashMap<String, Fraction>();
        }

        /*
         * If the system consists of a single equation, it is technically not a
         * system, but we make no such distincation and resolve it anyway.
         */
        // if (equations.size() == 1) {
        // return solveSingleEquation();
        // }

        /*
         * Solve a regular system. Begin with separating the system into
         * dependent and independent variables, by simply solving for as many
         * non-dummy variables as possible through regular substitution.
         */
        final List<Equation> equationsToSolve = new LinkedList<Equation>();
        equationsToSolve.addAll(equations);

        final Deque<Variable> variablesToSolve = new LinkedList<Variable>();
        for (final Variable variable : variableIndex.values()) {
            if (!(variable instanceof DummyVariable)) {
                variablesToSolve.add(variable);
            }
        }

        final Set<Variable> boundVariables = new HashSet<Variable>();
        final Set<Variable> unBoundVariables = new HashSet<Variable>();

        while (!equationsToSolve.isEmpty()) {
            final Variable variableToSolve = variablesToSolve.poll();

            for (final Equation equation : equationsToSolve) {

                if (constainsVariable(equation, variableToSolve)) {
                    final IExpression solution = equation.solveForVariable(variableToSolve);
                    substituteVariable(variableToSolve, solution);
                    equationsToSolve.remove(equation);
                    boundVariables.add(variableToSolve);
                    break;
                }
            }
        }

        /*
         * Create the set of unbound variables by taking the complement to the
         * set of bound ones.
         */
        for (final Variable variable : variableIndex.values()) {
            if (!boundVariables.contains(variable)) {
                unBoundVariables.add(variable);
            }
        }

        /*
         * Enforce restrictions on the variables.
         * 
         * FIXME: This is most likely NOT SOUND and may lead to highly
         * unpredicatble runtime behavior. The entire constraint system is too
         * haphazard.
         */
        for (final Variable variable : unBoundVariables) {
            for (final IRestriction restriction : restrictions.get(variable)) {
                restriction.makeConform(variable.evaluate());
            }
        }

        /*
         * Finally, compile a set of relevant, resulting values, and return it.
         */
        final Map<String, Fraction> valueMapping = new HashMap<String, Fraction>();
        for (final Variable variable : variableIndex.values()) {
            if (!(variable instanceof DummyVariable)) {
                valueMapping.put(variable.getName(), variable.evaluate());
            }
        }

        assert __debug_AssertCorrectness(valueMapping);

        return valueMapping;
    }

    private void substituteVariable(final Variable variableToSolve,
                                    final IExpression solution) {

        assert variableIndex.values().contains(variableToSolve);

        variableToSolve.bind(solution);
    }
}