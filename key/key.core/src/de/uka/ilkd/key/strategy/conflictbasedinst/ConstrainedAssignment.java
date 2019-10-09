package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.stream.Collectors;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

/**
 * A constrained assignment is a mapping from terms to terms stating equality
 * between mapped terms and a set of constraints on the key-terms.
 *
 * @author Andre Challier <andre.challier@stud.tu-darmstadt.de>
 *
 */
public class ConstrainedAssignment {

    private LinkedHashMap<Term, LinkedHashSet<Term>> assignments;
    private LinkedHashSet<Term> constraints;
    private LinkedHashMap<Term, LinkedHashSet<Term>> eqClassMap;
    private LinkedHashMap<Term, LinkedHashSet<Term>> uneqMap;
    private LinkedHashSet<Term> terms;
    private TermBuilder tb;

    public ConstrainedAssignment() {
        assignments = new LinkedHashMap<Term, LinkedHashSet<Term>>();
        constraints = new LinkedHashSet<Term>();
        eqClassMap = new LinkedHashMap<Term, LinkedHashSet<Term>>(ContextSingleton.getContext().getEqualityClassMap());
        uneqMap = new LinkedHashMap<Term, LinkedHashSet<Term>>(ContextSingleton.getContext().getUnequalityMap());
        tb = CbiServices.getTermBuiler();
    }

    public ConstrainedAssignment addConstraint(Term equation) {
        ConstrainedAssignment ca = copy();
        ca.constraints.add(equation);
        return ca;
    }

    public ConstrainedAssignment addAssignment(Term terma, Term termb) {
        assert terma.arity() == termb.arity() : "Can not add assignment with unequal arities";
        ConstrainedAssignment ca = copy();
        ca.assignments.computeIfAbsent(terma, map -> new LinkedHashSet<Term>()).add(termb);
        for(int i = 0; i < terma.arity(); i++) {
            Term constraint = tb.equals(terma.sub(i), termb.sub(i));
            ca.constraints.add(constraint);
        }
        return ca;
    }

    private ConstrainedAssignment copy() {
        ConstrainedAssignment ca = new ConstrainedAssignment();
        for(Map.Entry<Term, LinkedHashSet<Term>> equation : assignments.entrySet()) {
            ca.assignments.put(equation.getKey(), equation.getValue());
        }
        ca.constraints.addAll(constraints);
        return ca;
    }

    @Override
    public String toString() {
        String s = "CA{";
        for(Term term: assignments.keySet()) {
            for(Term eq : assignments.get(term)) {
                s = s + term.toString() + "=" + eq.toString() + ", ";
            }
        }
        s += constraints.stream().map(term -> term.toString()).collect(Collectors.joining(", ", " <>", ""));
        s += "}";
        return s;
    }

    public LinkedHashMap<Term, LinkedHashSet<Term>> getAssignments() {
        return assignments;
    }

    public LinkedHashSet<Term> getConstraints() {
        return constraints;
    }

    public LinkedHashSet<Term> getTerms() {
        if(terms == null) {
            terms = new LinkedHashSet<Term>();
            terms.addAll(constraints);
            assignments.forEach((a, set) -> set.forEach(b -> terms.add(tb.equals(a, b))));
        }
        return terms;
    }



}
