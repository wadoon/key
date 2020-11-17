package de.uka.ilkd.key.strategy.normalization.simple;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.strategy.normalization.Quantification;

import java.util.*;

class QuantifiedClauseSet {

    private final ClauseSet clauseSet;
    private final List<Quantification> quantifications;
    private final Map<Term, Term> skolemMap;

    public QuantifiedClauseSet(List<Quantification> quantifications, ClauseSet clauseSet,
                               Map<Term, Term> skolemMap) {
        this.quantifications = new LinkedList<Quantification>(quantifications);
        this.clauseSet = clauseSet;
        this.skolemMap = skolemMap;
    }

    public QuantifiedClauseSet(Literal literal) {
        this.clauseSet = new ClauseSet(new Clause(literal));
        this.quantifications = new LinkedList<Quantification>();
        this.skolemMap = new HashMap<Term, Term>();
    }

    public QuantifiedClauseSet(Quantifier quantifier, QuantifiableVariable qv,
                               QuantifiedClauseSet sub) {
        this.clauseSet = sub.clauseSet;
        this.quantifications = new LinkedList<Quantification>(Arrays.asList(new Quantification(quantifier, qv)));
        this.quantifications.addAll(sub.quantifications);
        this.skolemMap = new HashMap<>(sub.skolemMap);
    }

    public static QuantifiedClauseSet all(QuantifiableVariable qv, QuantifiedClauseSet sub) {
        List<Quantification> quantifications = new LinkedList<Quantification>();
        quantifications.add(new Quantification(Quantifier.ALL, qv));
        quantifications.addAll(sub.quantifications);
        return new QuantifiedClauseSet(quantifications, sub.clauseSet, sub.skolemMap);
    }

    public static QuantifiedClauseSet exists(QuantifiableVariable qv, Term qvt, Term skFun, QuantifiedClauseSet sub) {
        List<Quantification> quantifications = new LinkedList<Quantification>();
        quantifications.add(new Quantification(Quantifier.EX, qv));
        quantifications.addAll(sub.quantifications);
        Map<Term, Term> skMap = new HashMap<>(sub.skolemMap);
        skMap.put(qvt, skFun);
        return new QuantifiedClauseSet(quantifications, sub.clauseSet, sub.skolemMap);
    }

    public QuantifiedClauseSet(Term var, Term skFun, QuantifiedClauseSet sub) {
        this.clauseSet = sub.clauseSet;
        this.quantifications = new LinkedList<Quantification>(sub.quantifications);
        this.skolemMap = new HashMap<>(sub.skolemMap);
        skolemMap.put(var, skFun);
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
        HashMap<Term, Term> skolemMap = new HashMap<Term, Term>(this.skolemMap);
        skolemMap.putAll(qcs.skolemMap);
        return new QuantifiedClauseSet(quantifications, merge, skolemMap);
    }

    public ClauseSet getClauseSet() {
        return clauseSet;
    }

    public Map<Term, Term> getSkolemMap() { return skolemMap;}

    public List<Quantification> getQuantifications() {
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
