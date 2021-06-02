package keyext.extract_preconditions.projections;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import keyext.extract_preconditions.projections.visitors.LeaveOutTermConstructionVisitor;
import keyext.extract_preconditions.projections.visitors.TransitiveVarNameFinder;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.Set;

/**
 * This projection strategy removes any atom which contains unallowed variables.
 * Such removed atoms are substituted through suitable true/false values.
 * The strategy only processes the "boolean sceleton" of the term until all/existential quantifiers
 * or atoms are encountered.
 */
public class LeaveOutProjection extends AbstractTermProjection {
    private final ImmutableList<ProgramVariable> programVariables;

    private final boolean isTransitive;

    private final Set<Name> transitiveBlackList;

    /**
     * Constructor for LeaveOutProjection Strategy
     *
     * @param programVariablesParam The program variables that may appear in the resulting term
     * @param servicesParam The proof services (necessary for term building etc.)
     */
    public LeaveOutProjection(ImmutableList<ProgramVariable> programVariablesParam,
                              Services servicesParam) {
        this(programVariablesParam, servicesParam, false, null);
    }

    /**
     * Extended constructor for LeaveOUtProjection Strategy.
     * This constructor allows using a transitive set of variables for projection
     *
     * @param programVariablesParam The program variables that may appear in the resulting term
     * @param servicesParam The proof services (necessary for term building etc.)
     * @param transitive True if transitive closure of programVariablesParam should be used
     * @param varNameBlackList Blacklist of variables to ignore when using transitive closure
     */
    public LeaveOutProjection(ImmutableList<ProgramVariable> programVariablesParam,
                              Services servicesParam,
                              boolean transitive, Set<Name> varNameBlackList){
        super(servicesParam);
        this.isTransitive = transitive;
        this.programVariables = programVariablesParam;
        this.transitiveBlackList = varNameBlackList;
    }

    @Override
    public Term projectTerm(Term inputTerm) {
        if(inputTerm.op() instanceof Junctor && (inputTerm.op() == Junctor.TRUE || inputTerm.op() == Junctor.FALSE)) {
            return inputTerm;
        }
        ImmutableList<ProgramVariable> allowedVars = this.programVariables;
        if (this.isTransitive) {
            TransitiveVarNameFinder varNameVisitor = new TransitiveVarNameFinder(allowedVars, this.transitiveBlackList);
            inputTerm.execPostOrder(varNameVisitor);
            Set<ProgramVariable> allowedVarSet = varNameVisitor.getTransitiveVariableClosure();
            allowedVars = ImmutableSLList.nil();
            for (ProgramVariable var : allowedVarSet) {
                allowedVars = allowedVars.append(var);
            }
        }
        LeaveOutTermConstructionVisitor
            leaveOutVisitor = new LeaveOutTermConstructionVisitor(allowedVars, this.services.getTermBuilder());
        inputTerm.execPostOrder(leaveOutVisitor);
        return leaveOutVisitor.getTerm();
    }
}

