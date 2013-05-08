package se.gu.svanefalk.testgeneration.keystone.equations;

import java.util.Calendar;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.Semaphore;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.testgeneration.keystone.KeYStoneException;
import se.gu.svanefalk.testgeneration.keystone.equations.comparator.Equals;
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
    private static final IRestriction greaterThanZeroRestriction;
    private static final IRestriction integerValueRestriction;
    private static final RestrictionFactory restrictionFactory;
    static {
        restrictionFactory = RestrictionFactory.getInstance();
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
        
        RestrictionFactory restrictionFactory = RestrictionFactory.getInstance();

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
        Set<Equation> equations = new HashSet<>();
        for (Term term : terms) {

            /*
             * Convert the Term to an inequality.
             */
            IComparator inequality = expressionUtils.constructExpression(term,
                    variableIndex);

            /*
             * Convert the inequality to an equation.
             */
            Variable dummyVariable = ExpressionUtils.createDummyVariable();
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
        return new EquationSystem(equations, null, variableIndex);
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
}