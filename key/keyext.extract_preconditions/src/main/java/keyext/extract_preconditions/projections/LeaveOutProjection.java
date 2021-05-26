package keyext.extract_preconditions.projections;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.*;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.*;

public class LeaveOutProjection extends AbstractTermProjection {
    private ImmutableList<ProgramVariable> programVariables;

    public LeaveOutProjection(
        ImmutableList<ProgramVariable> programVariablesParam,
        Services servicesParam) {
        super(servicesParam);
        this.programVariables = programVariablesParam;
    }

    @Override
    public Term projectTerm(Term inputTerm) {
        LeaveOutTermConstructionVisitor leaveOutVisitor = new LeaveOutTermConstructionVisitor(programVariables, this.services.getTermBuilder());
        inputTerm.execPostOrder(leaveOutVisitor);
        return leaveOutVisitor.getTerm();
    }
}

/**
 * Constructs a new term which leaves out all non desired terms.
 * Called with execPostOrder
 */
class LeaveOutTermConstructionVisitor implements Visitor {

    private TermBuilder termBuilder;

    private Term constructedTerm;

    private Stack<List<Term>> termStorage;

    private Stack<Operator> currentOp;

    private ImmutableList<ProgramVariable> programVariables;

    private Term tt;

    private Term ff;

    public LeaveOutTermConstructionVisitor(
        ImmutableList<ProgramVariable> programVariablesParam,
        TermBuilder termBuilderParam) {
        this.termBuilder = termBuilderParam;
        this.constructedTerm = null;
        this.termStorage = new Stack<List<Term>>();
        this.currentOp = new Stack<Operator>();
        this.programVariables = programVariablesParam;
        this.tt = this.termBuilder.tt();
        this.ff = this.termBuilder.ff();
    }

    public Term getTerm() {
        return this.constructedTerm;
    }

    public Term currentDefaultVal() {
        Junctor current = (Junctor) this.currentOp.peek();
        if (current == Junctor.AND) {
            return this.tt;
        }
        if (current == Junctor.OR) {
            return this.ff;
        }
        if (current == Junctor.NOT) {
            Operator cache = this.currentOp.pop();
            this.swapTruthValues();
            Term rv = this.currentDefaultVal();
            this.currentOp.push(cache);
            this.swapTruthValues();
            return this.termBuilder.not(rv);
        }
        if (current == Junctor.IMP) {
            if (this.termStorage.peek().size() == 0) {
                // We are in the first part of implication
                return this.tt;
            } else {
                // We are in the second part of the implication
                return this.ff;
            }
        }
        return this.tt;
    }

    @Override
    public boolean visitSubtree(Term visited) {
        // TODO(steuber): What about (visited.op() instanceof Quantifier)?
        return (visited.op() instanceof Junctor);
    }

    private void swapTruthValues() {
        Term tmp = this.tt;
        this.tt = this.ff;
        this.ff = tmp;
    }

    @Override
    public void visit(Term visited) {
        boolean includeNode = true;
        if (!this.visitSubtree(visited)) {
            FindVarNamesVisitor varNamesVisitor = new FindVarNamesVisitor();
            visited.execPostOrder(varNamesVisitor);
            Set<ProgramVariable> foundVariables = varNamesVisitor.getVariables();
            // TODO(steuber): This check seems fishy. Is this how it is supposed to be done?
            for (ProgramVariable v : foundVariables) {
                boolean isParam = false;
                for (ProgramVariable param : this.programVariables) {
                    if (param.name().equals(v.name())) {
                        isParam = true;
                        break;
                    }
                }
                if (!isParam) {
                    includeNode = false;
                    break;
                }
            }
            if (foundVariables.size()==0) {
                includeNode = false;
            }
        }

        List<Term> currentTermList = this.termStorage.peek();
        if (includeNode) {
            currentTermList.add(visited);
        } else {
            currentTermList.add(this.currentDefaultVal());
        }
    }

    @Override
    public void subtreeEntered(Term subtreeRoot) {
        if (this.visitSubtree(subtreeRoot)) {
            this.termStorage.push(new LinkedList<Term>());
            this.currentOp.push(subtreeRoot.op());
            if (subtreeRoot.op()==Junctor.NOT) {
                this.swapTruthValues();
            }
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
            int childTermNum = childTerms.size() - 1;
            Term newTerm;
            if (childTermNum > 0) {
                childTerms.remove(childTermNum);
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
            if (this.termStorage.isEmpty()) {
                this.constructedTerm = newTerm;
            } else {
                this.termStorage.peek().add(newTerm);
            }
            if (subtreeRoot.op()==Junctor.NOT) {
                this.swapTruthValues();
            }
        }
    }
}

class FindVarNamesVisitor extends DefaultVisitor {

    private Set<ProgramVariable> foundVariables;

    public FindVarNamesVisitor(){
        foundVariables = new HashSet<ProgramVariable>();
    }

    public Set<ProgramVariable> getVariables() {
        return foundVariables;
    }

    @Override
    public void visit(Term visited) {
        if (visited.op() instanceof ProgramVariable) {
            this.foundVariables.add((ProgramVariable) visited.op());
        }
    }
}