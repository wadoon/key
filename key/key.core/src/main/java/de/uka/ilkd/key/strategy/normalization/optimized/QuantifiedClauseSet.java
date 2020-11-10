package de.uka.ilkd.key.strategy.normalization.optimized;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.strategy.normalization.Quantification;

import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;

public class QuantifiedClauseSet {

    private final ClauseSet clauseSet;
    private final LinkedList<Quantification> quantifications;

    public QuantifiedClauseSet(LinkedList<Quantification> quantifications, ClauseSet clauseSet) {
        this.quantifications = new LinkedList<Quantification>(quantifications);
        this.clauseSet = clauseSet;
    }

    public QuantifiedClauseSet(Literal literal) {
        this.clauseSet = new ClauseSet(new Clause(literal));
        this.quantifications = new LinkedList<Quantification>();
    }

    public QuantifiedClauseSet(Quantifier quantifier, QuantifiableVariable qv,
                               QuantifiedClauseSet sub) {
        this.clauseSet = sub.clauseSet;
        this.quantifications = new LinkedList<Quantification>(Arrays.asList(new Quantification(quantifier, qv)));
        this.quantifications.addAll(sub.quantifications);
    }

    public QuantifiedClauseSet and(QuantifiedClauseSet qcs) {
        return combine(qcs, this.clauseSet.and(qcs.clauseSet));
    }

    public QuantifiedClauseSet or(QuantifiedClauseSet qcs) {
        return combine(qcs, this.clauseSet.or(qcs.clauseSet));
    }

    private QuantifiedClauseSet combine(QuantifiedClauseSet qcs, ClauseSet merge) {
        LinkedList<Quantification> quantifications = new LinkedList<Quantification>(this.quantifications);
        // TODO error message if duplicate of quantified  variable
        quantifications.addAll(qcs.quantifications);
        return new QuantifiedClauseSet(quantifications, merge);
    }

    public ClauseSet getClauseSet() {
        return clauseSet;
    }

    public LinkedList<Quantification> getQuantifications() {
        return quantifications;
    }

    Term toTerm(TermBuilder tb) {
        return toTerm(quantifications.iterator(), clauseSet.toTerm(tb), tb);
    }

    private Term toTerm(Iterator<Quantification> iterator, Term term, TermBuilder tb) {
        if(!iterator.hasNext()) {
            return term;
        }
        Quantification qt = iterator.next();
        return qt.getQuantifier() == Quantifier.ALL ? tb.all(qt.getQuantifiedVariable(), toTerm(iterator, term, tb))
                : tb.ex(qt.getQuantifiedVariable(), toTerm(iterator, term, tb));
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("QCS[{");
        for(Quantification qt : quantifications) {
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
