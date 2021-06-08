package keyext.extract_preconditions.projections.visitors;

import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import java.util.HashSet;
import java.util.Set;

/**
 * Visitor which collects all visited ProgramVariables
 */
class FindVarNamesVisitor extends DefaultVisitor {

    /**
     * The set of all found variables
     */
    private final Set<ProgramVariable> foundVariables;

    /**
     * Constructor for a FindVarNamesVisitor.
     */
    public FindVarNamesVisitor() {
        foundVariables = new HashSet<>();
    }

    /**
     * Returns all collected ProgramVariables
     * Must only be called after visiting terms
     *
     * @return A set of all collected variables.
     */
    public Set<ProgramVariable> getVariables() {
        return foundVariables;
    }

    @Override
    public void visit(Term visited) {
        if (visited.op() instanceof ProgramVariable) {
            ProgramVariable var = (ProgramVariable) visited.op();
            this.foundVariables.add(var);
        }
    }
}
