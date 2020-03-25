package de.uka.ilkd.key.strategy.normalization;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;

import java.util.Iterator;

public class QuantifiedClauseSet {

    private final ClauseSet clauseSet;
    private final ImmutableList<QuantifiedTerm> quantifiedTerms;

    public QuantifiedClauseSet(ImmutableList<QuantifiedTerm> quantifiedTerms, ClauseSet clauseSet) {
        this.quantifiedTerms = quantifiedTerms;
        this.clauseSet = clauseSet;
    }

    public QuantifiedClauseSet(Literal literal) {
        this.clauseSet = new ClauseSet(DefaultImmutableSet.<Clause>nil().add(new Clause(literal)));
        this.quantifiedTerms = DefaultImmutableSet.<QuantifiedTerm>nil().toImmutableList();
    }

    public QuantifiedClauseSet(Quantifier quantifier, QuantifiableVariable qv,
                               QuantifiedClauseSet sub) {
        this.clauseSet = sub.clauseSet;
        this.quantifiedTerms = DefaultImmutableSet.<QuantifiedTerm>nil().toImmutableList()
                        .append(new QuantifiedTerm(quantifier, qv))
                        .append(sub.quantifiedTerms);
    }

    public QuantifiedClauseSet and(QuantifiedClauseSet qcs) {
        return new QuantifiedClauseSet(this.quantifiedTerms.append(qcs.quantifiedTerms), this.clauseSet.and(qcs.clauseSet));
    }

    public QuantifiedClauseSet or(QuantifiedClauseSet qcs) {
        return new QuantifiedClauseSet(this.quantifiedTerms.append(qcs.quantifiedTerms), this.clauseSet.or(qcs.clauseSet));
    }

    public ClauseSet getClauseSet() {
        return clauseSet;
    }

    public ImmutableList<QuantifiedTerm> getQuantifiedTerms() {
        return quantifiedTerms;
    }

    Term toTerm(TermBuilder tb) {
        return toTerm(quantifiedTerms.iterator(), clauseSet.toTerm(tb), tb);
    }

    private Term toTerm(Iterator<QuantifiedTerm> iterator, Term term, TermBuilder tb) {
        if(!iterator.hasNext()) {
            return term;
        }
        QuantifiedTerm qt = iterator.next();
        return qt.getQuantifier() == Quantifier.ALL ? tb.all(qt.getQuantifiedVariable(), toTerm(iterator, term, tb))
                : tb.ex(qt.getQuantifiedVariable(), toTerm(iterator, term, tb));
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("QCS[{");
        for(QuantifiedTerm qt : quantifiedTerms) {
            sb.append(qt.getQuantifiedVariable().toString());
            sb.append(", ");
        }
        sb.delete(sb.length() -2, sb.length());
        sb.append("},");
        sb.append(clauseSet.toString());
        sb.append("]");
        return sb.toString();
    }
}
