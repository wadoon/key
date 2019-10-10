package de.uka.ilkd.key.strategy.conflictbasedinst.normalization;

import java.util.Iterator;
import java.util.LinkedHashSet;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;

public class QuantifiedClauseSet {

    private ClauseSet cs;
    private ImmutableList<QuantifiedTerm> quantifiers;

    private QuantifiedClauseSet(ClauseSet cs,
            ImmutableList<QuantifiedTerm> quantifiers) {
        this.cs = cs;
        this.quantifiers = quantifiers;
    }

    public static QuantifiedClauseSet create(Literal lit) {
        return new QuantifiedClauseSet(ClauseSet.fromLiteral(lit), DefaultImmutableSet.<QuantifiedTerm> nil().toImmutableList());
    }

    public static QuantifiedClauseSet create(Quantifier quantifier, QuantifiableVariable qv,
            QuantifiedClauseSet sub) {
        return new QuantifiedClauseSet(sub.cs,
                DefaultImmutableSet.<QuantifiedTerm> nil().toImmutableList()
                        .append(new QuantifiedTerm(quantifier, qv))
                        .append(sub.quantifiers));
    }

    public static QuantifiedClauseSet create(ImmutableList<QuantifiedTerm> quantifiers, ClauseSet cs) {
        return new QuantifiedClauseSet(cs, quantifiers);
    }

    public Term toTerm(TermBuilder tb) {
        return toTerm(quantifiers.iterator(), cs.toTerm(tb), tb);
    }

    private Term toTerm(Iterator<QuantifiedTerm> it, Term term,
            TermBuilder tb) {
        if (!it.hasNext())
            return term;
        QuantifiedTerm qt = it.next();

        return qt.getQuantifier() == Quantifier.ALL ? tb.all(qt.getQv(), toTerm(it, term, tb))
                : tb.ex(qt.getQv(), toTerm(it, term, tb));
    }

    public QuantifiedClauseSet and(QuantifiedClauseSet qcs) {
        return new QuantifiedClauseSet(this.cs.and(qcs.cs), this.quantifiers.append(qcs.quantifiers));
    }

    public QuantifiedClauseSet or(QuantifiedClauseSet qcs) {
        return new QuantifiedClauseSet(this.cs.or(qcs.cs), this.quantifiers.append(qcs.quantifiers));
    }

    public ImmutableList<QuantifiedTerm> getQuantifiers() {
        return quantifiers;
    }

    public ClauseSet getClauseSet() {
        return cs;
    }

    private LinkedHashSet<Literal> grounds = null;

    public LinkedHashSet<Literal> getGroundLiterals(TermBuilder tb) {
        if(grounds != null) return grounds;
        grounds = new LinkedHashSet<Literal>();
        LinkedHashSet<Term> qTerms = getQuantifiersAsTerms(tb);
        for(Clause clause: cs.getClauses()) {
            grounds.addAll(clause.getGroundLiterals(qTerms));
        }
        return grounds;
    }

    public LinkedHashSet<Clause> getUnquantifiedClauses(TermBuilder tb) {
        LinkedHashSet<Clause> unqClauses = new LinkedHashSet<Clause>();
        if(quantifiers.isEmpty()) {
            for(Clause clause : cs.getClauses()) {
                unqClauses.add(clause);
            }
            return unqClauses;
        }
        LinkedHashSet<Term> quantified = new LinkedHashSet<Term>();
        for(QuantifiedTerm qt : quantifiers) {
            quantified.add(tb.var(qt.getQv()));
        }

        for(Clause clause : cs.getClauses()) {
            if(!clause.contains(quantified)) {
                unqClauses.add(clause);
            }
        }
        return unqClauses;
    }

    private LinkedHashSet<Term> qTerms = null;

    public LinkedHashSet<Term> getQuantifiersAsTerms(TermBuilder tb) {
        if(qTerms != null) return qTerms;
        qTerms = new LinkedHashSet<Term>();
        for(QuantifiedTerm qt : quantifiers) {
            qTerms.add(tb.var(qt.getQv()));
        }
        return qTerms;
    }

    public QuantifiedClauseSet invert() {
        QuantifiedClauseSet inversion = new QuantifiedClauseSet(cs.invert(), this.quantifiers);
        return inversion;
    }

    @Override
    public String toString() {
        String ret = quantifiers.toString();
        ret += cs.toString();
        return ret;
    }



}
