package se.gu.svanefalk.testgeneration.keystone.equations;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import se.gu.svanefalk.testgeneration.keystone.KeYStoneException;
import se.gu.svanefalk.testgeneration.keystone.equations.comparator.Equals;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Variable;
import se.gu.svanefalk.testgeneration.keystone.equations.restriction.IRestriction;
import se.gu.svanefalk.testgeneration.util.parsers.TermParserTools;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * Instances of this class represent a system of equations.
 * 
 * @author christopher
 * 
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
         * Create the variable index
         */
        Map<String, Variable> variableIndex = new HashMap<>();
        for (Term term : terms) {
            term.execPreOrder(new VariableCollector(variableIndex));
        }

        /*
         * Create the equations
         */
        ExpressionUtils expressionBuilder = ExpressionUtils.getInstance();
        Set<Equals> equations = new HashSet<>();
        for (Term term : terms) {

            /*
             * Convert the Term to an inequality.
             */
            IComparator inequality = expressionBuilder.constructExpression(
                    term, variableIndex);

            /*
             * Convert the inequality to an equation.
             */
            Equals equality = expressionBuilder.removeInequality(inequality,
                    variableIndex);

            equations.add(equality);
        }

        return new EquationSystem(equations, null, variableIndex);
    }

    /**
     * The equations present in the system.
     */
    Set<Equals> equations = null;

    /**
     * Auxiliary restrictions on the system, imposed by KeYStone and evaluated
     * separately.
     */
    List<IRestriction> restrictions = null;

    /**
     * An index of the variables present in the system.
     */
    Map<String, Variable> variableIndex = null;

    private EquationSystem(Set<Equals> equations,
            List<IRestriction> restrictions, Map<String, Variable> variableIndex) {
        super();
        this.equations = equations;
        this.restrictions = restrictions;
        this.variableIndex = variableIndex;
    }

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