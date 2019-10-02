package de.uka.ilkd.key.strategy.conflictbasedinst.normalization;

import java.util.LinkedHashSet;
import java.util.LinkedList;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

/**
 * A ClauseSet is a set of clauses. In term representation clauses are
 * conjuncted. A clause set will never contain any universal clause. A clause
 * set is immutable, every method will return a fresh clause set.
 *
 * @author Andre Challier <andre.challier@stud.tu-darmstadt.de>
 *
 */
public class ClauseSet {

    private ImmutableSet<Clause> clauses;

    private ClauseSet() {
        clauses = DefaultImmutableSet.<Clause> nil();
    }

    private ClauseSet(ImmutableSet<Clause> clauses) {
        this.clauses = clauses;
    }

    public static ClauseSet fromLiteral(Literal lit) {
        ClauseSet cs = new ClauseSet();
        return cs.and(Clause.fromLiteral(lit));
    }

    public ClauseSet and(ClauseSet cs) {
        if(cs.clauses.size() == 0) return this;
        // TODO evaluate clauses, (A) & (!A) --> FALSE (could be removed then)
        return new ClauseSet(clauses.union(cs.clauses));
    }

    public ClauseSet and(Clause clause) {
        if (clause == Clause.UNIVERSAL_CLAUSE)
            return new ClauseSet(clauses);
        return new ClauseSet(clauses.add(clause));
    }

    public ClauseSet or(ClauseSet cs) {
        // TODO evaluate clauses, (A) & (!A) --> FALSE (could be removed then)
        LinkedHashSet<Clause> clauseSet = new LinkedHashSet<Clause>();
        for (Clause cl_a : clauses) {
            for (Clause cl_b : cs.clauses) {
                clauseSet.add(cl_a.or(cl_b));
            }
        }
        return new ClauseSet(DefaultImmutableSet.fromSet(clauseSet));
    }

    public ClauseSet or(Clause clause) {
        LinkedHashSet<Clause> clauseSet = new LinkedHashSet<Clause>();
        for(Clause cl : clauses) {
            clauseSet.add(cl.or(clause));
        }
        return new ClauseSet(DefaultImmutableSet.fromSet(clauseSet));
    }

    public Term toTerm(TermBuilder tb) {
        LinkedList<Term> terms = new LinkedList<Term>();
        clauses.forEach(clause -> terms.add(clause.toTerm(tb)));
        return tb.and(terms);
    }

}
