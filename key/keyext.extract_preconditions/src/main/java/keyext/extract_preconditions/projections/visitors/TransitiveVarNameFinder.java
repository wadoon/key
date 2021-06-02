package keyext.extract_preconditions.projections.visitors;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import org.key_project.util.collection.ImmutableList;

import java.util.HashSet;
import java.util.Set;

/**
 * Compute the transitive closure of program variables
 */
public class TransitiveVarNameFinder extends VarNameVisitor {

    private ImmutableList<ProgramVariable> variablesOfInterest;

    private Set<ProgramVariable> transitiveVariableClosure;

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
    public TransitiveVarNameFinder(ImmutableList<ProgramVariable> variablesOfInterest,
                                   Set<Name> transitiveBlackList) {
        this.variablesOfInterest = variablesOfInterest;
        this.transitiveVariableClosure = new HashSet<>();
        this.transitiveVarNameClosure = new HashSet<>();
        for (ProgramVariable var : this.variablesOfInterest) {
            this.transitiveVariableClosure.add(var);
            this.transitiveVarNameClosure.add(var.name());
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
    public Set<ProgramVariable> getTransitiveVariableClosure() {
        return this.transitiveVariableClosure;
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
            oldSize = this.transitiveVariableClosure.size();
            super.visit(visited);
        } while(this.transitiveVariableClosure.size()!=oldSize);
        this.inVisitLoop = false;
    }

    @Override
    public void handleVariables(Set<ProgramVariable> variablesFound) {
        boolean isParam = false;
        for (ProgramVariable v : variablesFound) {
            if (this.transitiveVarNameClosure.contains(v.name())
                && !this.transitiveBlackList.contains(v.name())) {
                isParam = true;
                break;
            }
        }
        if (isParam) {
            for (ProgramVariable var : variablesFound) {
                if (!this.transitiveBlackList.contains(var.name())) {
                    this.transitiveVariableClosure.add(var);
                    this.transitiveVarNameClosure.add(var.name());
                }
            }
        }
    }
}
