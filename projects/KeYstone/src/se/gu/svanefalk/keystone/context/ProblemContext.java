package se.gu.svanefalk.keystone.context;

import java.util.HashSet;
import java.util.Set;

import se.gu.svanefalk.testgeneration.util.parsers.TermParserTools;

import de.uka.ilkd.key.logic.Term;

/**
 * Represents a container of metadata related to the problem currently being
 * solved.
 * 
 * @author christopher
 * 
 */
public class ProblemContext {

    /**
     * The set of problems to be solved during this session.
     */
    private final Set<Problem> problems = new HashSet<Problem>();

    /**
     * The variables involved in this problem,
     */
    private final Set<Number> variables = new HashSet<Number>();

    /**
     * Constructs a new context for a problem.
     * 
     * @param term
     *            the problem (represented as a {@link Term}).
     * @return the problem context
     */
    public static ProblemContext constructContext(Term problem) {

        return null;
    }

    /**
     * Collect all variables present in the current problem.
     * 
     * @param problem
     *            the problem
     * @return the set of variables in the problem
     */
    private static Set<Number> collectVariables(Term problem) {

        if (TermParserTools.isAnd(problem)) {

        }
        return null;
    }
}
