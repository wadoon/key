package se.gu.svanefalk.testgeneration.keystone.equations;

import java.util.ArrayList;
import java.util.Calendar;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.naming.OperationNotSupportedException;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.testgeneration.keystone.KeYStoneException;
import se.gu.svanefalk.testgeneration.keystone.equations.comparator.Equals;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.DummyVariable;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.NumericConstant;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Variable;
import se.gu.svanefalk.testgeneration.keystone.equations.restriction.IRestriction;
import se.gu.svanefalk.testgeneration.keystone.equations.restriction.RestrictionFactory;
import se.gu.svanefalk.testgeneration.util.parsers.TermParserTools;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Term;

/**
 * Instances of this class represent a system of equations.
 * 
 * @author christopher
 * 
 */
public class EquationSystem {

    /*
     * Make common field static for better performance (for some reason,
     * Fractions are very expensive to create for large numbers).
     */
    private static final Fraction maxInteger;
    private static final Fraction minInteger;

    private static final NumericConstant baseIntegerValue;

    private static final IRestriction greaterThanZeroRestriction;
    private static final IRestriction integerValueRestriction;

    private static final RestrictionFactory restrictionFactory;

    static {
        restrictionFactory = RestrictionFactory.getInstance();

        baseIntegerValue = new NumericConstant(new Fraction(1));

        maxInteger = new Fraction(Integer.MAX_VALUE);
        minInteger = new Fraction(Integer.MIN_VALUE);
        integerValueRestriction = restrictionFactory.createRangeRestriction(
                minInteger, maxInteger);
        greaterThanZeroRestriction = restrictionFactory.createGreaterOrEqualsRestriction(new Fraction(
                0));
    }

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

        long time = Calendar.getInstance().getTimeInMillis();

        Map<Variable, List<IRestriction>> restrictions = new HashMap<>();

        /*
         * Create the variable index
         */
        Map<String, Variable> variableIndex = new HashMap<>();
        for (Term term : terms) {
            term.execPreOrder(new VariableCollector(variableIndex));
        }

        /*
         * Impose basic restrictions on the variables
         */
        for (Variable variable : variableIndex.values()) {
            List<IRestriction> variableRestrictions = restrictions.get(variable);
            if (variableRestrictions == null) {
                variableRestrictions = new LinkedList<>();
                restrictions.put(variable, variableRestrictions);
            }
            variableRestrictions.add(integerValueRestriction);
        }

        /*
         * Create the equations
         */
        ExpressionUtils expressionUtils = ExpressionUtils.getInstance();
        List<Equation> equations = new ArrayList<>();
        for (Term term : terms) {

            /*
             * Convert the Term to an inequality.
             */
            IComparator inequality = expressionUtils.constructExpression(term,
                    variableIndex);

            /*
             * Convert the inequality to an equation.
             */
            Variable dummyVariable = DummyVariable.createDummyVariable();
            Equals equality = expressionUtils.createEqualityFromInequality(
                    inequality, variableIndex, dummyVariable);
            Equation equation = Equation.createEquation(equality);
            equations.add(equation);

            /*
             * Impose restrictions on the dummy variable created current
             * equation.
             */
            List<IRestriction> dummyVariableRestrictions = restrictions.get(dummyVariable);
            if (dummyVariableRestrictions == null) {
                dummyVariableRestrictions = new LinkedList<>();
                restrictions.put(dummyVariable, dummyVariableRestrictions);
            }
            dummyVariableRestrictions.add(integerValueRestriction);
            dummyVariableRestrictions.add(greaterThanZeroRestriction);

            System.out.println("Create system: "
                    + (Calendar.getInstance().getTimeInMillis() - time));
        }

        /*
         * Sort the resulting equations according to number of variables.
         */
        Collections.sort(equations, EquationSetSorter.getInstance());
        Set<Equation> equationSet = new LinkedHashSet<>();
        for (Equation equation : equations) {
            equationSet.add(equation);
        }

        return new EquationSystem(equationSet, restrictions, variableIndex);
    }

    public Map<String, Fraction> solveSystem()
            throws OperationNotSupportedException {

        /*
         * Empty systems should not occur, but we accomodate them just in case.
         */
        if (equations.isEmpty()) {
            return new HashMap<>();
        }

        /*
         * If the system consists of a single equation, it is technically not a
         * system, but we make no such distincation and resolve it anyway.
         */
        if (equations.size() == 1) {
            return solveSingleEquation();
        }

        /*
         * Solve a regular system. Begin with separating the system into
         * dependent and independent variables, by simply solving for as many
         * non-dummy variables as possible through regular substitution.
         */
        List<Equation> equationsToSolve = new LinkedList<>();
        equationsToSolve.addAll(equations);

        Deque<Variable> variablesToSolve = new LinkedList<>();
        for (Variable variable : variableIndex.values()) {
            if (!(variable instanceof DummyVariable)) {
                variablesToSolve.add(variable);
            }
        }

        Set<Variable> boundVariables = new HashSet<>();
        Set<Variable> unBoundVariables = new HashSet<>();

        while (!equationsToSolve.isEmpty()) {
            Variable variableToSolve = variablesToSolve.poll();

            for (Equation equation : equationsToSolve) {

                if (constainsVariable(equation, variableToSolve)) {
                    IExpression solution = equation.solveForVariable(variableToSolve);
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
        for (Variable variable : variableIndex.values()) {
            if (!boundVariables.contains(variable)) {
                unBoundVariables.add(variable);
            }
        }

        /*
         * Assign arbitrary values to the set of unbound variables.
         */
        for (Variable variable : unBoundVariables) {
            variable.bind(baseIntegerValue);
        }

        /*
         * Enforce restrictions on the variables.
         * 
         * FIXME: This is most likely NOT SOUND and may lead to highly
         * unpredicatble runtime behavior. The entire constraint system is too
         * haphazard.
         */
        for (Variable variable : unBoundVariables) {
            for (IRestriction restriction : restrictions.get(variable)) {
                restriction.makeConform(variable.evaluate());
            }
        }

        /*
         * Finally, compile a set of relevant, resulting values, and return it.
         */
        Map<String, Fraction> valueMapping = new HashMap<>();
        for (Variable variable : variableIndex.values()) {
            if (!(variable instanceof DummyVariable)) {
                valueMapping.put(variable.getName(), variable.evaluate());
            }
        }

        assert __debug_AssertCorrectness(valueMapping);

        return valueMapping;
    }

    private boolean __debug_AssertCorrectness(Map<String, Fraction> valueMapping)
            throws OperationNotSupportedException {
        resetAllVariables();

        for (String setVariableIdentifier : valueMapping.keySet()) {
            Variable variableToBind = variableIndex.get(setVariableIdentifier);
            NumericConstant valueToBind = new NumericConstant(
                    valueMapping.get(variableToBind));
            variableToBind.bind(valueToBind);
        }

        for (Equation equation : equations) {
            if (!equation.evaluate()) {
                return false;
            }
        }

        return true;
    }

    private void resetAllVariables() {
        for (Variable variable : variableIndex.values()) {
            variable.bind(null);
        }
    }

    private void substituteVariable(Variable variableToSolve,
            IExpression solution) {

        assert variableIndex.values().contains(variableToSolve);

        variableToSolve.bind(solution);
    }

    /**
     * @param equation
     * @param variablesToSolve
     * @return true if the equation contains the variable, false otherwise.
     *         Reference based comparisons are enforced.
     */
    private boolean constainsVariable(Equation equation,
            Variable variableToSolve) {

        for (Variable variable : equation.getVariables()) {
            if (variable == variableToSolve) {
                return true;
            }
        }
        return false;
    }

    private Map<String, Fraction> solveSingleEquation() {
        // TODO Auto-generated method stub
        return null;
    }

    /**
     * The equations present in the system.
     */
    Set<Equation> equations = null;

    /**
     * Auxiliary restrictions on the system, imposed by KeYStone and evaluated
     * separately.
     */
    Map<Variable, List<IRestriction>> restrictions = null;

    /**
     * An index of the variables present in the system.
     */
    Map<String, Variable> variableIndex = null;

    private EquationSystem(Set<Equation> equations,
            Map<Variable, List<IRestriction>> restrictions,
            Map<String, Variable> variableIndex) {
        super();
        this.equations = equations;
        this.restrictions = restrictions;
        this.variableIndex = variableIndex;
    }

    /**
     * Instances of this visitor are used in order to extract variables from a
     * {@link Term}, encoding them as {@link Variable} instances.
     * 
     * @author christopher
     * 
     */
    private static class VariableCollector extends DefaultVisitor {

        private final Map<String, Variable> variableIndex;

        public VariableCollector(Map<String, Variable> variableIndex) {
            super();
            this.variableIndex = variableIndex;
        }

        @Override
        public void visit(final Term visited) {
            if (TermParserTools.isProgramVariable(visited)) {
                String variableName = visited.toString();
                variableIndex.put(variableName, new Variable(variableName));
            }
        }
    }

    /**
     * Used for sorting {@link Equation} instances with regard to how many
     * variables the contain.
     * 
     * @author christopher
     * 
     */
    private static class EquationSetSorter implements Comparator<Equation> {

        private static EquationSetSorter instance = null;

        public static EquationSetSorter getInstance() {

            if (EquationSetSorter.instance == null) {
                EquationSetSorter.instance = new EquationSetSorter();
            }
            return EquationSetSorter.instance;
        }

        private EquationSetSorter() {

        }

        @Override
        public int compare(Equation o1, Equation o2) {
            return o1.getVariables().size() - o2.getVariables().size();
        }
    }
}