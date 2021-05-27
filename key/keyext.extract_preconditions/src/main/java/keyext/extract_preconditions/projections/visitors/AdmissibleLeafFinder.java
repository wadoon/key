package keyext.extract_preconditions.projections.visitors;

import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import org.key_project.util.collection.ImmutableList;

import java.util.Set;

/**
 * Visitor which checks whether the visited node is admissible, i.e. it should be included
 * in a projection on the given variables.
 *
 * For each term a new visitor should be generated.
 */
public class AdmissibleLeafFinder extends DefaultVisitor {

    /**
     * Variables allowed within the projection
     */
    private final ImmutableList<ProgramVariable> allowedVariables;

    /**
     * True if term is admissible
     */
    private boolean isAdmissible;

    /**
     * Constructor for the AdmissibleLeafFinder.
     * A new visitor should be generated for each term that is visited.
     * The visitor checks whether there are any leafs which only contain allowedVariables
     *
     * @param allowedVariablesParam Variables allowed in the projection.
     */
    public AdmissibleLeafFinder(ImmutableList<ProgramVariable> allowedVariablesParam) {
        this.isAdmissible = false;
        this.allowedVariables = allowedVariablesParam;
    }

    /**
     * Returns true the node is admissible.
     * Must only be called after the term was visited.
     * @return
     */
    public boolean isAdmissible() {
        return this.isAdmissible;
    }

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
            // TODO(steuber): This check seems fishy. Is this how it is supposed to be done?
            for (ProgramVariable v : foundVariables) {
                boolean isParam = false;
                for (ProgramVariable param : this.allowedVariables) {
                    if (param.name().equals(v.name())) {
                        isParam = true;
                        break;
                    }
                }
                if (!isParam) {
                    return;
                }
            }
            if (foundVariables.size() == 0) {
                return;
            }
            // If we reach this point we have a node which only had admissible variables...
            this.isAdmissible = true;
        }
    }
}
