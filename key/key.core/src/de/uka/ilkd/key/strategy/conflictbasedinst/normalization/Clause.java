package de.uka.ilkd.key.strategy.conflictbasedinst.normalization;

import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Objects;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Junctor;

public class Clause {

    public static final Clause UNIVERSAL_CLAUSE = new UniversalClause();
    private ImmutableSet<Literal> literals;

    private Clause() {
        literals = DefaultImmutableSet.<Literal>nil();
    }

    public Clause(ImmutableSet<Literal> literals) {
        this.literals = literals;
    }

    public static Clause fromLiteral(Literal literal) {
        Clause clause = new Clause();
        clause.literals = clause.literals.add(literal);
        return clause;
    }

    public Clause or(Literal literal) {

        if(literal.getTerm().op() == Junctor.FALSE) {
            if(literal.getPolarity()) {
                return this;
            }else {
                return UNIVERSAL_CLAUSE;
            }
        }

        if(literal.getTerm().op() == Junctor.TRUE) {
            if(literal.getPolarity()) {
                return UNIVERSAL_CLAUSE;
            }else {
                return this;
            }
        }

        // A | !A --> TRUE
        if(literals.contains(literal.complement())) {
            return UNIVERSAL_CLAUSE;
        }

        Clause clause = new Clause();
        clause.literals = literals.add(literal);
        return clause;

    }

    public Clause or(Clause clause) {
        if(clause == UNIVERSAL_CLAUSE) return UNIVERSAL_CLAUSE;
        Clause ret = new Clause();
        ret.literals = literals;
        for(Literal lit: clause.literals) {
            ret = ret.or(lit);
        }
        return ret;
    }

    public Term toTerm(TermBuilder tb) {
        return tb.or(termList(tb));
    }

    private List<Term> termList(TermBuilder tb) {
        LinkedList<Term> terms = new LinkedList<Term>();
        literals.forEach(lit -> terms.add(lit.toTerm(tb)));
        return terms;
    }



    @Override
    public int hashCode() {
        return Objects.hash(literals);
    }

    @Override
    public boolean equals(Object obj) {
        if(obj == this) return true;
        if(!(obj instanceof Clause)) return false;
        Clause other = (Clause) obj;
        return this.literals.equals(other.literals);
    }

    @Override
    public String toString() {
        return literals.toString();
    }



    private static class UniversalClause extends Clause {

        public UniversalClause() {
            super();
        }

        @Override
        public Clause or(Literal literal) {
            return this;
        }

        @Override
        public Clause or(Clause clause) {
            return this;
        }

        @Override
        public Term toTerm(TermBuilder tb) {
            return tb.tt();
        }

    }



    public ImmutableSet<Literal> getLiterals() {
        return literals;
    }

    public boolean contains(LinkedHashSet<Term> quantified) {
        for(Literal lit: literals) {
            Term term = lit.getTerm();
            if(contains(quantified, term)) return true;
        }
        return false;
    }

    public static boolean contains(LinkedHashSet<Term> quantified, Term term) {
        if(quantified.contains(term)) return true;
        if(term.arity() == 0) return false;
        for(Term sub : term.subs()) {
            if(contains(quantified, sub)) return true;
        }
        return false;
    }

    // !(a | b | c) --> !a & !b & !c
    public ClauseSet invert() {
        LinkedHashSet<Clause> cs = new LinkedHashSet<Clause>();
        for(Literal lit: literals) {
            cs.add(Clause.fromLiteral(lit.complement()));
        }
        return ClauseSet.create(DefaultImmutableSet.fromSet(cs));
    }


}
