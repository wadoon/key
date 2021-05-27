package keyext.extract_preconditions.projections.visitors;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import org.key_project.util.collection.ImmutableList;

import java.util.LinkedList;
import java.util.List;
import java.util.Stack;

/**
 * Constructs a new term which leaves out all non desired terms.
 * LeaveOutTermConstructionVisitor is not reusable, please generate a new Visitor for each term.
 * Called with execPostOrder
 */
public class LeaveOutTermConstructionVisitor implements Visitor {

    /**
     * Term Builder (necessary for construction of new term)
     */
    private final TermBuilder termBuilder;

    /**
     * The resulting constructed term
     */
    private Term constructedTerm;

    /**
     * Stack of Lists containing terms saved at current level for term construction
     */
    private final Stack<List<Term>> termStorage;

    /**
     * Stack of Operations encountered during visitation
     */
    private final Stack<Operator> currentOp;

    /**
     * Allowed program variables
     */
    private final ImmutableList<ProgramVariable> programVariables;

    /**
     * Constructor for the LeaveOutTermConstructionVisitor.
     * Note, that we need a new visitor for each term that is visited.
     *
     * @param programVariablesParam Program variables that are allowed
     * @param termBuilderParam Term Builder (necessary for construction of new term)
     */
    public LeaveOutTermConstructionVisitor(
        ImmutableList<ProgramVariable> programVariablesParam,
        TermBuilder termBuilderParam) {
        this.termBuilder = termBuilderParam;
        this.programVariables = programVariablesParam;
        this.constructedTerm = null;
        this.termStorage = new Stack<>();
        this.currentOp = new Stack<>();
    }

    /**
     * Returns the generated term.
     * Must only be called after the term was visited
     *
     * @return The generated (projected) term
     */
    public Term getTerm() {
        return this.constructedTerm;
    }

    /**
     * Returns a default value for the current position in the term.
     * E.g. when visiting a conjunction this function returns true because
     * x AND TRUE reduces to x
     *
     * @return The default value for the current term
     */
    private Term currentDefaultVal() {
        Junctor current;
        if (!this.currentOp.empty()) {
            current = (Junctor) this.currentOp.peek();
        } else {
            current = null;
        }
        if (current == Junctor.AND) {
            return this.termBuilder.tt();
        }
        if (current == Junctor.OR) {
            return this.termBuilder.ff();
        }
        if (current == Junctor.NOT) {
            Operator cache = this.currentOp.pop();
            Term rv = this.currentDefaultVal();
            this.currentOp.push(cache);
            return this.termBuilder.not(rv);
        }
        if (current == Junctor.IMP) {
            if (this.termStorage.peek().size() == 0) {
                // We are in the first part of implication
                return this.termBuilder.tt();
            } else {
                // We are in the second part of the implication
                return this.termBuilder.ff();
            }
        }
        return this.termBuilder.tt();
    }

    /**
     * Adds a node at the current position.
     * The term is either added to the corresponding position in termStorage or to consturctedTerm
     * if termStorage is empty already
     * @param toAdd Term to store
     */
    private void addNodeAtCurPos(Term toAdd) {
        if (this.termStorage.isEmpty()) {
            this.constructedTerm = toAdd;
        } else {
            this.termStorage.peek().add(toAdd);
        }
    }

    @Override
    public boolean visitSubtree(Term visited) {
        // TODO(steuber): What about (visited.op() instanceof Quantifier)?
        if (!(visited.op() instanceof  Junctor)) {
            return false;
        }
        return shouldIncludeNode(visited);
    }

    /**
     * Checks whether the current term should be included in the resulting term.
     * To this end, the AdmissibleLeafFinder is used which checks whether any leafs of the term
     * are relevant for the projection.
     * In this case by "leafs" we mean term nodes at the end of the boolean sceleton consisting of
     * junctions
     *
     * @param visited Node currently visisted
     * @return true if node should be included
     */
    private boolean shouldIncludeNode(Term visited) {
        AdmissibleLeafFinder admissibilityVisitor = new AdmissibleLeafFinder(this.programVariables);
        visited.execPostOrder(admissibilityVisitor);

        return admissibilityVisitor.isAdmissible();
    }

    @Override
    public void visit(Term visited) {
        boolean includeNode = this.shouldIncludeNode(visited);
        if (includeNode) {
            this.addNodeAtCurPos(visited);
        } else {
            if(visited.op() instanceof Junctor && (visited.op() == Junctor.TRUE || visited.op() == Junctor.FALSE)) {
                this.addNodeAtCurPos(visited);
            }
            this.addNodeAtCurPos(this.currentDefaultVal());
        }
    }

    @Override
    public void subtreeEntered(Term subtreeRoot) {
        if (this.visitSubtree(subtreeRoot)) {
            this.termStorage.push(new LinkedList<>());
            this.currentOp.push(subtreeRoot.op());
        }
    }

    @Override
    public void subtreeLeft(Term subtreeRoot) {
        // TODO(steuber): Simplifications!
        if (this.visitSubtree(subtreeRoot)) {
            this.currentOp.pop();
            List<Term> childTerms = this.termStorage.pop();
            // We also visit the node itself so we need to drop the last element again
            // (or only add this last once if there are no children)
            // TODO(steuber): Do this more elegantly?
            Term newTerm;
            if (childTerms.size() > 1) {
                childTerms.remove(childTerms.size()-1);
                // TODO(steuber): createTerm does not support NOT => Is this on purpose?
                if (subtreeRoot.op() == Junctor.NOT) {
                    assert childTerms.size() == 1;
                    newTerm = this.termBuilder.not(childTerms.get(0));
                } else {
                    newTerm = this.termBuilder.tf().createTerm(subtreeRoot.op(), childTerms);
                }
            } else {
                newTerm = this.termBuilder.tf().createTerm(subtreeRoot.op());
            }
            this.addNodeAtCurPos(newTerm);
        }
    }
}
