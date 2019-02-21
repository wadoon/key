package de.uka.ilkd.key.logic;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Predicate;

/**
 * A visitor filtering {@link Term}s.
 *
 * @author Dominic Steinhoefel
 */
public class FilterVisitor extends DefaultVisitor {
    private final Predicate<Term> filter;
    private List<Term> result = new ArrayList<>();

    public FilterVisitor(Predicate<Term> filter) {
        this.filter = filter;
    }

    @Override
    public void visit(Term visited) {
        if (filter.test(visited)) {
            result.add(visited);
        }
    }

    public List<Term> result() {
        return result;
    }
}