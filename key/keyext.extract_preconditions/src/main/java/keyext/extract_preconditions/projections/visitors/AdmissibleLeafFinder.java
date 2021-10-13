package keyext.extract_preconditions.projections.visitors;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import org.key_project.util.collection.ImmutableList;

import java.util.Set;

/**
 * Visitor which checks whether the visited node is admissible, i.e. it should be included
 * in a projection on the given variables.
 *
 * For each term a new visitor should be generated.
 */
public class AdmissibleLeafFinder extends VarNameVisitor {

    /**
     * Variables allowed within the projection
     */
    private final ImmutableList<Name> allowedVariables;

    /**
     * True if term is admissible
     */
    private boolean isAdmissible;

    /**
     * Variable Names that will be ignored
     */
    private Set<Name> blacklist;

    /**
     * Constructor for the AdmissibleLeafFinder.
     * A new visitor should be generated for each term that is visited.
     * The visitor checks whether there are any leafs which only contain allowedVariables
     *
     * @param allowedVariablesParam Variables allowed in the projection.
     * @param blacklist
     */
    public AdmissibleLeafFinder(ImmutableList<Name> allowedVariablesParam,
                                Set<Name> blacklist) {
        this.isAdmissible = false;
        this.allowedVariables = allowedVariablesParam;
        this.blacklist = blacklist;
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
    public void handleVariables(Set<Name> foundVariables,
                                Set<ProgramVariable> variablesFound,
                                Set<Function> foundFunctions) {
        boolean consideredVariables = false;
        for (Name curName : foundVariables) {
            if (this.blacklist.contains(curName)) {
                continue;
            }
            consideredVariables=true;
            if (!this.allowedVariables.contains(curName)) {
                return;
            }
        }
        if (!consideredVariables) { // If all variables were skipped, we must not admit this term
            return;
        }
        // If we reach this point we have a node which only had admissible variables...
        this.isAdmissible = true;
    }
}
