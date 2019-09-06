package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.stream.Collectors;

import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;

public class Context {

    private TermBuilder tb;
    private LinkedHashSet<Term> literals;
    private LinkedHashSet<Term> terms;
    private HashMap<Operator, LinkedHashSet<Term>> functionMap;
    private HashMap<Term, LinkedHashSet<Term>> eqClassMap;

    protected Context(Term formula, Sequent sequent) {
        this.literals = new LinkedHashSet<Term>();
        this.terms = new LinkedHashSet<Term>();
        this.tb = TermBuilderHolder.getInstance().getTermBuilder();
        this.functionMap = new LinkedHashMap<Operator, LinkedHashSet<Term>>();
        this.eqClassMap = new LinkedHashMap<Term, LinkedHashSet<Term>>();
        extractGroundLiterals(sequent.antecedent(), formula, true);
        extractGroundLiterals(sequent.succedent(), formula, false);
    }

    private void extractGroundLiterals(Semisequent semiseq, Term formula,
            boolean polarity) {
        for (SequentFormula sf : semiseq) {
            // ignore quantified formula
            if (sf.formula() == formula)
                continue;
            extractGroundLiterals(sf.formula(), polarity);
        }
    }

    private void extractGroundLiterals(Term term, boolean polarity) {
        if (term.op() == Equality.EQUALS && TermHelper.isGround(term)) {
            addLiteral(term, polarity);
        }
        else if (term.op() == Junctor.NOT) {
            extractGroundLiterals(term.sub(0), !polarity);
        }
        else if (term.op() == Junctor.AND) {
            term.subs().forEach(sub -> extractGroundLiterals(sub, polarity));
        }
    }

    private void addLiteral(Term literal, boolean polarity) {
        literals.add(polarity ? literal : tb.not(literal));
        literal.subs().forEach(sub -> addAllTerm(sub));
        if(polarity) {
            addToEqClass(literal.sub(0), literal.sub(1));
        }
    }

    private void addToEqClass(Term a, Term b) {
        mergeEqClasses(a,b);
    }

    private LinkedHashSet<Term> getEqClass(Term term) {
        return eqClassMap.computeIfAbsent(term, eqClass -> new LinkedHashSet<Term>(Arrays.asList(term)));
    }

    private void mergeEqClasses(Term a, Term b) {
        LinkedHashSet<Term> eqClass = getEqClass(a);
        eqClass.addAll(getEqClass(b));
        eqClassMap.put(b, eqClass);
    }

    public LinkedHashSet<Term> getEqClassOf(Term term) {
        return eqClassMap.get(term);
    }

    private void addAllTerm(Term term) {
        addTerm(term);
        term.subs().forEach(sub -> addAllTerm(sub));
    }

    private void addTerm(Term term) {
        // terms that are not functions can be ignored as they are not
        // matched anyways
        System.out.println("Evaluating: " + term.toString() + " op: " + term.op() + " opclass: " + term.op().getClass().getSimpleName());
        if (term.op() instanceof Function) {
            System.out.println("Adding " + term.toString());
            terms.add(term);
            addToFunctionMap(term);
        }else {
            System.out.println("not adding " + term.toString());
        }
    }

    private void addToFunctionMap(Term term) {
        functionMap.computeIfAbsent(term.op(), set -> new LinkedHashSet<Term>()).add(term);
    }

    public String toString() {
        String s = "Literals: ";
        s += literals.stream().map(term -> term.toString()).collect(Collectors.joining(", ", "{", "}"));
        s += " functions: ";
        s += functionMap.keySet().stream().map(op -> op.toString()).collect(Collectors.joining(", ", "{" , "}"));
        s += " eq classes: ";
        s += eqClassMap.toString();
        return s;
    }

    public boolean satisfies(Term formula) {
        if(literals.contains(formula)) {
            return true;
        }else if(TermHelper.isTrue(formula)) {
            return true;
        }else if(TermHelper.isFalse(formula)) {
            return false;
        }else {
            return false;
        }
    }

    public boolean satisfies(Term funA, Term funB) {
        assert funA.op() instanceof Function && funB.op() instanceof Function : "Can only test satisfaction of eqality of functions";
        return false;
    }

    public LinkedHashSet<Term> getMatchingLiterals(Term constraint) {
        return functionMap.getOrDefault(constraint.op(), new LinkedHashSet<Term>());
    }
}
