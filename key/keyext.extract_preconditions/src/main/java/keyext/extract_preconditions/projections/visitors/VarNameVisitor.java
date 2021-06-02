package keyext.extract_preconditions.projections.visitors;

import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import java.util.Set;

/**
 * Abstract Visitor which allows handling ProgramVariables found in a non-junction term
 */
public abstract class VarNameVisitor extends DefaultVisitor {

    @Override
    public boolean visitSubtree(Term visited) {
        return (visited.op() instanceof Junctor);
    }

    @Override
    public void visit(Term visited) {
        if (!(visited.op() instanceof Junctor)) {
            FindVarNamesVisitor leafVisitor = new FindVarNamesVisitor();
            visited.execPostOrder(leafVisitor);
            Set<ProgramVariable> foundVariables = leafVisitor.getVariables();
            this.handleVariables(foundVariables);
        }
    }

    /**
     * Method which handles the variables found in the a non junction term
     * @param variablesFound
     */
    public abstract void handleVariables(Set<ProgramVariable> variablesFound);
}
