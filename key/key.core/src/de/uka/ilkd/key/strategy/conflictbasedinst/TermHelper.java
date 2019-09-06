package de.uka.ilkd.key.strategy.conflictbasedinst;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.sort.Sort;

class TermHelper {

    private static TermBuilder tb() {
        return TermBuilderHolder.getInstance().getTermBuilder();
    }

    private static TermFactory tf() {
        return null;
    }

    public static Term negate(Term term) {
        return tb().not(term);
    }

    public static Term quantVar(String name, Sort sort) {
        return tb().var(new LogicVariable(new Name(name), sort));
    }

    public static boolean isGround(Term term) {
        for(Term sub: term.subs()) {
            if(!isGround(sub)) return false;
        }
        return !(term.op() instanceof QuantifiableVariable);
    }

    public static boolean isNullary(Term term) {
        return term.subs().size() == 0;
    }

    public static boolean isQuantifiedVariable(Term term) {
        return  term.op() instanceof QuantifiableVariable;
    }

    public static boolean isFunction(Term term) {
        return term.op() instanceof Function;
    }

    public static boolean isEquality(Term term) {
        return term.op() == Equality.EQUALS;
    }

    public static boolean isNegation(Term term) {
        return term.op() == Junctor.NOT;
    }

    public static boolean isOr(Term term) {
        return term.op() == Junctor.OR;
    }

    public static boolean isAnd(Term term) {
        return term.op() == Junctor.AND;
    }

    public static boolean isImp(Term term) {
        return term.op() == Junctor.IMP;
    }

    public static boolean isTrue(Term term) {
        return term.op() == Junctor.TRUE;
    }

    public static boolean isFalse(Term term) {
        return term.op() == Junctor.FALSE;
    }

    public static boolean isAll(Term term) {
        return term.op() == Quantifier.ALL;
    }

    public static boolean isExists(Term term) {
        return term.op() == Quantifier.EX;
    }

}
