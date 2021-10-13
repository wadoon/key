package keyext.extract_preconditions.projections.visitors;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import org.key_project.util.collection.ImmutableList;

import java.util.HashSet;
import java.util.Set;

/**
 * Compute the transitive closure of program variables
 */
public class TransitiveVarNameFinder extends VarNameVisitor {

    private ImmutableList<Name> variablesOfInterest;

    private Set<Name> transitiveVarNameClosure;

    private Set<Name> transitiveBlackList;

    private boolean inVisitLoop;


    /**
     * Initiate a visitor for transitive variable name finding
     *
     * @param variablesOfInterest Variables that build the basis for the computation of the
     *                            transitive closure
     * @param transitiveBlackList Variables which should be ignored during computation
     */
    public TransitiveVarNameFinder(ImmutableList<Name> variablesOfInterest,
                                   Set<Name> transitiveBlackList) {
        this.variablesOfInterest = variablesOfInterest;
        this.transitiveVarNameClosure = new HashSet<>();
        for (Name curName : this.variablesOfInterest) {
            this.transitiveVarNameClosure.add(curName);
        }
        this.inVisitLoop = false;
        this.transitiveBlackList = transitiveBlackList;
    }

    /**
     * Returns the transitive closure.
     * Must only be called after visitation took place
     *
     * @return A set containing the transitive closure of program variables
     */
    public Set<Name> getTransitiveVariableClosure() {
        return this.transitiveVarNameClosure;
    }

    /**
     * Modified visit procedure.
     * Visitation of root node may be executed multiple times if necessary to compute convex hull
     *
     * @param visited Term to visit
     */
    @Override
    public void visit(Term visited) {
        // TODO(steuber): This is the naive approach. If this is a performance bottleneck we may
        // want to use something like BFS/DFS by building a graph first
        if (this.inVisitLoop) {
            super.visit(visited);
            return;
        }
        this.inVisitLoop = true;
        int oldSize;
        do {
            oldSize = this.transitiveVarNameClosure.size();
            super.visit(visited);
        } while(this.transitiveVarNameClosure.size()!=oldSize);
        this.inVisitLoop = false;
    }

    @Override
    public void handleVariables(Set<Name> foundVariables,
                                Set<ProgramVariable> variablesFound,
                                Set<Function> foundFunctions) {
        boolean isParam = false;
        for (Name curName : foundVariables) {
            if (this.transitiveVarNameClosure.contains(curName)
                && !this.transitiveBlackList.contains(curName)) {
                isParam = true;
                break;
            }
        }
        if (isParam) {
            for (Name curName : foundVariables) {
                if (!this.transitiveBlackList.contains(curName)) {
                    this.transitiveVarNameClosure.add(curName);
                }
            }
        }
    }
}
