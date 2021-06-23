package keyext.extract_preconditions.projections.visitors;

import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Junctor;

import java.util.Stack;

public class JunctorSimplificationVisitor extends DefaultVisitor {

    private Stack<Term> termStack;

    private TermBuilder tb;

    public JunctorSimplificationVisitor(TermBuilder tb) {
        this.termStack = new Stack<>();
        this.tb = tb;
    }

    public Term getSimplified() {
        assert termStack.size()>0;
        return termStack.peek();
    }

    @Override
    public void visit(Term visited) {
        Term result;
        if (visited.op() instanceof Junctor) {
            result = handleJunctor(visited, (Junctor) visited.op());
        } else {
            cleanup(visited);
            result = visited;
        }
        termStack.push(result);
    }

    private void cleanup(Term visited) {
        for (int i = 0; i< visited.arity(); i++) {
            this.termStack.pop();
        }
    }

    private Term handleJunctor(Term visited, Junctor currentJunctor) {
        if (currentJunctor==Junctor.AND) {
            return handleAnd(visited);
        }
        if (currentJunctor==Junctor.OR) {
            return handleOr(visited);
        }
        if (currentJunctor == Junctor.NOT) {
            return handleNot(visited);
        }
        cleanup(visited);
        return visited;
    }

    private Term handleNot(Term visited) {
        Term part1 = this.termStack.pop();
        if (part1.op()==Junctor.TRUE) {
            return this.tb.ff();
        }
        if (part1.op()==Junctor.FALSE) {
            return this.tb.tt();
        }
        return this.tb.not(part1);
    }

    private Term handleOr(Term visited) {
        Term part1 = this.termStack.pop();
        Term part2 = this.termStack.pop();
        if (part1.op()==Junctor.TRUE || part2.op()==Junctor.TRUE) {
            return this.tb.tt();
        }
        if (part1.op()==Junctor.FALSE) {
            return part2;
        }
        if (part2.op()==Junctor.FALSE) {
            return part1;
        }
        return this.tb.or(part2, part1);
    }

    private Term handleAnd(Term visited) {
        Term part1 = this.termStack.pop();
        Term part2 = this.termStack.pop();
        if (part1.op()==Junctor.FALSE || part2.op()==Junctor.FALSE) {
            return this.tb.ff();
        }
        if (part1.op()==Junctor.TRUE) {
            return part2;
        }
        if (part2.op()==Junctor.TRUE) {
            return part1;
        }
        return this.tb.and(part2,part1);
    }
}
