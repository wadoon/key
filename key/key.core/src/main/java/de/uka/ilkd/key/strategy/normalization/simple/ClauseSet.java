package de.uka.ilkd.key.strategy.normalization.simple;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

import java.util.HashSet;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

/**
 * A Simple Clause Set is a set of objects of type {@link Clause} that is an implicit conjunction of all
 * contained clauses.
 */
class ClauseSet {

    private final HashSet<Clause> clauses;

    ClauseSet(Clause clause) {
        this.clauses = new HashSet<Clause>();
        this.clauses.add(clause);
    }

    private ClauseSet(HashSet<Clause> clauses) {
        this.clauses = clauses;
    }

    public HashSet<Clause> getClauses() {
        // this class is immutable so return only a copy of the clauseset
        return copyClauses();
    }

    public HashSet<Clause> copyClauses() {
        return new HashSet<Clause>(clauses);
    }

    /**
     * (c1 & ... & cn) & (d1 & ...& dn) => (c1 & ... & cn & d1 & ... & d_n)
     * @param clauseSet
     * @return
     */
    public ClauseSet and(ClauseSet clauseSet) {
        HashSet<Clause> conjunction = copyClauses();
        conjunction.addAll(clauseSet.getClauses());
        return new ClauseSet(conjunction);
    }

    /**
     * (c1 & ... & cn) | (d1 & ...& dn) => ((c1 | d1) & ... & (c1 | dn) & ... & (cn | d1) & ... & (cn | dn))
     * @param cs
     * @return
     */
    public ClauseSet or(ClauseSet cs) {
        HashSet<Clause> clauseSet = new HashSet<>();
        for (Clause outer : clauses) {
            for (Clause inner : cs.clauses) {
                clauseSet.add(outer.or(inner));
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
