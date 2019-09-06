package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.LinkedHashSet;
import java.util.stream.Collectors;

import de.uka.ilkd.key.logic.Term;

/**
 * Matching constraints are equalities between terms of a quantified
 * @author Andre Challier <andre.challier@stud.tu-darmstadt.de>
 *
 */
public class MatchingConstraints {

    /**
     *
     */
    private static final long serialVersionUID = 1L;

    private LinkedHashSet<Term> constraints;

    private MatchingConstraints() {
        constraints = new LinkedHashSet<Term>();
    }

    public static MatchingConstraints extractFrom(Term formula) {
        MatchingConstraints mc = new MatchingConstraints();
        mc.addAllTerms(formula);
        return mc;
    }

    private static MatchingConstraints empty() {
        return new MatchingConstraints();
    }

    private void addAllTerms(Term term) {
        term.subs().forEach(sub -> addAllTerms(sub));
        if(TermHelper.isFunction(term)) {
            constraints.add(term);
        }
    }

    public MatchingConstraints without(Term... terms) {
        MatchingConstraints mc = new MatchingConstraints();
        mc.constraints.addAll(constraints);
        for(Term term: terms) {
            mc.constraints.remove(term);
        }
        return mc;
    }

    public MatchingConstraints without(Iterable<Term> terms) {
        MatchingConstraints mc = new MatchingConstraints();
        mc.constraints.addAll(constraints);
        for(Term term: terms) {
            mc.constraints.remove(term);
        }
        return mc;
    }

    public MatchingConstraints only(Term... terms) {
        MatchingConstraints mc = new MatchingConstraints();
        for(Term term: terms) {
            if(constraints.contains(term)) mc.constraints.add(term);
        }
        return mc;
    }

    public MatchingConstraints only(Iterable<Term> terms) {
        MatchingConstraints mc = new MatchingConstraints();
        for(Term term: terms) {
            if(constraints.contains(term)) mc.constraints.add(term);
        }
        return mc;
    }

    public MatchingConstraints union(MatchingConstraints other) {
        MatchingConstraints mc = new MatchingConstraints();
        mc.constraints.addAll(other.constraints);
        mc.constraints.addAll(constraints);
        return mc;
    }

    public Term getFirst() {
        return constraints.iterator().next();
    }

    public boolean isEmpty() {
        return constraints.isEmpty();
    }

    @Override
    public String toString() {
        return constraints.stream().map(term -> term.toString()).collect(Collectors.joining(", ", "MC{", "}"));
    }


}
