package se.gu.svanefalk.keystone.equations;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import se.gu.svanefalk.testgeneration.keystone.equations.comparator.Equals;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Variable;
import se.gu.svanefalk.testgeneration.keystone.equations.restriction.IRestriction;
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

    private EquationSystem() {
    }

    /**
     * An index of the variables present in the system.
     */
    Set<Variable> variables = new HashSet<>();

    /**
     * The equations present in the system.
     */
    Set<Equals> equations = new HashSet<>();

    /**
     * Auxiliary restrictions on the system, imposed by KeYStone and evaluated
     * separately.
     */
    List<IRestriction> restrictions = new LinkedList<>();

    /**
     * Constructs a system of equations from a set of term representing either
     * equations or inequalities. All inequalities are converted by introducing
     * slack/surplus variables.
     * 
     * @param terms
     * @return
     */
    public static EquationSystem createEquationSystem(Collection<Term> terms) {

        for (Term term : terms) {

            if (TermParserTools.isEquals(term)) {

            } else if (TermParserTools.isGreaterOrEquals(term)) {

            } else if (TermParserTools.isLessOrEquals(term)) {

            } else {
                throw new IllegalArgumentException(
                        "Term does not represent an equals, greater-or-equals or less-or-equals operation: "
                                + term);
            }
        }
        return null;
    }

    /**
     * Instances of this visitor converts a {@link Term} into an equivalent
     * equation.
     * 
     * @author christopher
     * 
     */
    private static class EquationBuilder extends DefaultVisitor {

        
        
        @Override
        public void visit(Term visited) {

            if(TermParserTools.isEquals(visited)) {
                
            }
        }
    }
}