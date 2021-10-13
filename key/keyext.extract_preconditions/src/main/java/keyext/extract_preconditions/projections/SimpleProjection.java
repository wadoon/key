package keyext.extract_preconditions.projections;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import keyext.extract_preconditions.projections.visitors.SimpleLeaveOutTermConstructionVisitor;

public class SimpleProjection extends AbstractTermProjection {

    /**
     * Constructor for LeaveOutProjection Strategy
     *
     * @param programVariablesParam The program variables that may appear in the resulting term
     * @param servicesParam The proof services (necessary for term building etc.)
     */
    public SimpleProjection(Services servicesParam) {
        super(servicesParam);
    }

    @Override
    public Term projectTerm(Term inputTerm) {
        if(inputTerm.op() instanceof Junctor && (inputTerm.op() == Junctor.TRUE || inputTerm.op() == Junctor.FALSE)) {
            return inputTerm;
        }
        SimpleLeaveOutTermConstructionVisitor
            leaveOutVisitor = new SimpleLeaveOutTermConstructionVisitor(this.services.getTermBuilder());
        inputTerm.execPostOrder(leaveOutVisitor);
        return leaveOutVisitor.getTerm();
    }
}
