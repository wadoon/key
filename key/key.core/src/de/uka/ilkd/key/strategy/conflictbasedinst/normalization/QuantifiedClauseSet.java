package de.uka.ilkd.key.strategy.conflictbasedinst.normalization;

import java.util.Iterator;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

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

    public static QuantifiedClauseSet createAll(QuantifiableVariable qv,
            QuantifiedClauseSet sub) {
        return new QuantifiedClauseSet(sub.cs,
                DefaultImmutableSet.<QuantifiedTerm> nil().toImmutableList()
                        .append(QuantifiedTerm.createAll(qv))
                        .append(sub.quantifiers));
    }

    public static QuantifiedClauseSet createEx(QuantifiableVariable qv,
            QuantifiedClauseSet sub) {
        return new QuantifiedClauseSet(sub.cs,
                DefaultImmutableSet.<QuantifiedTerm> nil().toImmutableList()
                        .append(QuantifiedTerm.createEx(qv))
                        .append(sub.quantifiers));
    }

    public Term toTerm(TermBuilder tb) {
        return toTerm(quantifiers.iterator(), cs.toTerm(tb), tb);
    }

    private Term toTerm(Iterator<QuantifiedTerm> it, Term term,
            TermBuilder tb) {
        if (!it.hasNext())
            return term;
        QuantifiedTerm qt = it.next();
        return qt.isAll() ? tb.all(qt.qv, toTerm(it, term, tb))
                : tb.ex(qt.qv, toTerm(it, term, tb));
    }

    private static class QuantifiedTerm {

        private final boolean all;
        private final QuantifiableVariable qv;

        private QuantifiedTerm(boolean all, QuantifiableVariable qv) {
            this.all = all;
            this.qv = qv;
        }

        public static QuantifiedTerm createAll(QuantifiableVariable qv) {
            return new QuantifiedTerm(true, qv);
        }

        public static QuantifiedTerm createEx(QuantifiableVariable qv) {
            return new QuantifiedTerm(false, qv);
        }

        public boolean isAll() {
            return all;
        }

    }

    public QuantifiedClauseSet and(QuantifiedClauseSet qcs) {
        return new QuantifiedClauseSet(this.cs.and(qcs.cs), this.quantifiers.append(qcs.quantifiers));
    }

    public QuantifiedClauseSet or(QuantifiedClauseSet qcs) {
        return new QuantifiedClauseSet(this.cs.or(qcs.cs), this.quantifiers.append(qcs.quantifiers));
    }

}
