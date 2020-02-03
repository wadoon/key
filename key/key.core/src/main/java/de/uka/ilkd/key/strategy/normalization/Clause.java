package de.uka.ilkd.key.strategy.normalization;


import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import java.util.Arrays;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

/**
 * A Clause is finite set of literals [l<sub>1</sub>, l<sub>2</sub>, ... , l<sub>n</sub>] for natural n representing
 * the disjunction l<sub>1</sub> &or; l<sub>2</sub> &or; ... &or; l<sub>n</sub>. In this implementation this is an
 * immutable set of literal objects which makes a clause also immutable.
 *
 * @author Andre Challier <andre.challier@stud.tu-darmstadt.de>
 */
public class Clause {

    private final ImmutableSet<Literal> literals;

    public static final Clause EMPTY_CLAUSE = new Clause();

    Clause(Literal... literals) {
        this.literals = DefaultImmutableSet.fromSet(Arrays.stream(literals).collect(Collectors.toSet()));
    }

    Clause(ImmutableSet<Literal> literals) {
        this.literals = literals;
    }

    public ImmutableSet<Literal> getLiterals() {
        return this.literals;
    }

    public Clause or(Literal literal) {
        return new Clause(literals.add(literal));
    }

    public Clause or(Clause clause) {
        Clause  ret = new Clause(literals);
        clause.literals.forEach(literal -> ret.or(literal));
        return ret;
    }

    public boolean isHornClause() {
        for(Literal literal: literals) {
            if(literal.isPositive()) {return true;}
        }
        return false;
    }

    public Term toTerm(TermBuilder termBuilder) {
        return termBuilder.or(StreamSupport.stream(literals.spliterator(),false).map(literal -> literal.toTerm(termBuilder)).collect(Collectors.toList()));
    }
}
