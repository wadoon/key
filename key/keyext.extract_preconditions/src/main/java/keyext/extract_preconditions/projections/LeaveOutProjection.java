package keyext.extract_preconditions.projections;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import keyext.extract_preconditions.projections.visitors.LeaveOutTermConstructionVisitor;
import org.key_project.util.collection.ImmutableList;

/**
 * This projection strategy removes any atom which contains unallowed variables.
 * Such removed atoms are substituted through suitable true/false values.
 * The strategy only processes the "boolean sceleton" of the term until all/existential quantifiers
 * or atoms are encountered.
 */
public class LeaveOutProjection extends AbstractTermProjection {
    private final ImmutableList<ProgramVariable> programVariables;

    /**
     * Constructor for LeaveOutProjection Strategy
     *
     * @param programVariablesParam The program variables that may appear in the resulting term
     * @param servicesParam The proof services (necessary for term building etc.)
     */
    public LeaveOutProjection(
        ImmutableList<ProgramVariable> programVariablesParam,
        Services servicesParam) {
        super(servicesParam);
        this.programVariables = programVariablesParam;
    }

    @Override
    public Term projectTerm(Term inputTerm) {
        if(inputTerm.op() instanceof Junctor && (inputTerm.op() == Junctor.TRUE || inputTerm.op() == Junctor.FALSE)) {
            return inputTerm;
        }
        LeaveOutTermConstructionVisitor
            leaveOutVisitor = new LeaveOutTermConstructionVisitor(programVariables, this.services.getTermBuilder());
        inputTerm.execPostOrder(leaveOutVisitor);
        return leaveOutVisitor.getTerm();
    }
}

