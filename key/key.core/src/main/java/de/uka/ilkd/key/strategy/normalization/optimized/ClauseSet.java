package de.uka.ilkd.key.strategy.normalization.optimized;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

import java.util.HashSet;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

/**
 * A Simple Clause Set is a set of objects of type {@link Clause} that is an implicit conjunction of all
 * contained clauses.
 */
public class ClauseSet {

    private final HashSet<Clause> clauses;

    private final int hashCode;

    ClauseSet(Clause clause) {
        this.clauses = new HashSet<Clause>();
        this.clauses.add(clause);
        this.hashCode =  clauses.hashCode();
    }

    private ClauseSet(HashSet<Clause> clauses) {
        this.clauses = clauses;
        this.hashCode = clauses.hashCode();
    }

    public HashSet<Clause> getClauses() {
        // this class is immutable so return only a copy of the clauseset
        return new HashSet<Clause>(clauses);
    }

    public ClauseSet and(ClauseSet clauseSet) {
        HashSet<Clause> result = getClauses();
        result.addAll(clauseSet.getClauses());
        return new ClauseSet(result);
    }

    public ClauseSet or(ClauseSet cs) {
        HashSet<Clause> clauseSet = new HashSet<>();
        for (Clause cl_a : clauses) {
            for (Clause cl_b : cs.clauses) {
                clauseSet.add(cl_a.or(cl_b));
            }
        }
        return new ClauseSet(clauseSet);
    }

    public ClauseSet or(Clause clause) {
        HashSet<Clause> result = new HashSet<Clause>();
        for(Clause cl : clauses) {
            result.add(cl.or(clause));
        }
        return new ClauseSet(result);
    }

    public Term toTerm(TermBuilder termBuilder){
        return termBuilder.and(StreamSupport.stream(clauses.spliterator(), false).map(clause -> clause.toTerm(termBuilder)).collect(Collectors.toList()));
    }

    public String toString() {
        return "ClauseSet: "  + print(clauses);
    }

    @Override
    public int hashCode() {
        return hashCode;
    }

    private String print(HashSet<Clause> clauses) {
        StringBuilder sb = new StringBuilder();
        sb.append("[");
        for(Clause clause: clauses) {
            sb.append(clause.toString());
            sb.append(", ");
        }
        if(sb.length() > 1) {
            sb.delete(sb.length() -2, sb.length());
        }
        sb.append("]");
        return sb.toString();
    }
}
