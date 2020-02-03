package de.uka.ilkd.key.strategy.normalization;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

public class ClauseSet {

    private final ImmutableSet<Clause> clauses;

    public ClauseSet(ImmutableSet<Clause> clauses) {
        this.clauses = clauses;
    }

    public ClauseSet(Clause... clauses) {
        this.clauses = DefaultImmutableSet.fromSet(Arrays.stream(clauses).collect(Collectors.toSet()));
    }

    public ClauseSet and(ClauseSet clauseSet) {
        return new ClauseSet(clauseSet.clauses.union(clauses));
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
        LinkedHashSet<Clause> tempSet = new LinkedHashSet<Clause>();
        for(Clause cl : clauses) {
            tempSet.add(cl.or(clause));
        }
        return new ClauseSet(DefaultImmutableSet.fromSet(tempSet));
    }

    public ImmutableSet<Clause> getClauses() {
        return clauses;
    }

    public Term toTerm(TermBuilder termBuilder){
        return termBuilder.and(StreamSupport.stream(clauses.spliterator(), false).map(clause -> clause.toTerm(termBuilder)).collect(Collectors.toList()));
    }
}
