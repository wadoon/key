package de.uka.ilkd.key.strategy.normalization.simple;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

import java.util.Arrays;
import java.util.HashSet;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

class Clause {

    private final HashSet<Literal> literals;

    Clause(Literal literal) {
        this(new HashSet<Literal>(Arrays.asList(literal)));
    }

    private Clause(HashSet<Literal> literals) {
        this.literals = literals;
    }

    public HashSet<Literal> getLiterals() {
        return new HashSet<Literal>(literals);
    }

    public Clause or(Literal literal) {
        HashSet<Literal> result = new HashSet<Literal>(literals);
        result.add(literal);
        return new Clause(result);
    }

    public Clause or(Clause clause) {
        HashSet<Literal> result = new HashSet<Literal>(literals);
        result.addAll(clause.getLiterals());
        return new Clause(result);
    }

    public Term toTerm(TermBuilder builder) {
        return builder.or(StreamSupport.stream(literals.spliterator(), false).map(literal -> literal.toTerm(builder)).collect(Collectors.toList()));
    }

    public String toString() {
        return "Clause" + print(literals);
    }

    private String print(HashSet<Literal> literals) {
        StringBuilder sb = new StringBuilder();
        sb.append("[");
        for (Literal literal : literals) {
            sb.append(literal.toString());
            sb.append(", ");
        }
        if (sb.length() > 1) {
            sb.delete(sb.length() - 2, sb.length());
        }
        sb.append("]");
        return sb.toString();
    }
}
