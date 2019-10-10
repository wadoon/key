package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.LinkedHashSet;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.sort.Sort;

public class TermHelper {

    private static TermBuilder tb() {
        return CbiServices.getTermBuiler();
    }

    private static TermFactory tf() {
        return CbiServices.getTermFactory();
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

    public static boolean isEquiv(Term term) {
        return term.op() == Equality.EQV;
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

    public static boolean isLiteral(Term term) {
        return (term.op() == Junctor.NOT) ?
                isAtom(term.sub(0)):
                isAtom(term);
    }

    public static boolean isAtom(Term term) {
        final Operator op = term.op();
        return !(op instanceof Junctor
                || op == Equality.EQV
                || op instanceof IfThenElse
                || op instanceof Quantifier);
    }

    public static boolean containsEqualityInScope(Term term) {
        if(term.op() == Equality.EQUALS) return true;
        if(term.op() instanceof Junctor || term.op() == Quantifier.ALL || term.op() == Equality.EQV || term.op() == IfThenElse.IF_THEN_ELSE) {
            for(Term sub : term.subs()) {
                if(containsEqualityInScope(sub)) return true;
            }
        }
        return false;
    }

    public static Term replaceAll(Term term, Term grnd, Term subst) {
        if(subst.equals(term)) return grnd;
        if(subst.subs().size() == 0) return subst;
        Term[] subs = new Term[subst.subs().size()];
        for(int i = 0; i < subst.subs().size(); i++) {
            subs[i] = replaceAll(term, grnd, subst.subs().get(i));
        }
        return tf().createTerm(subst.op(), new ImmutableArray<Term>(subs), subst.boundVars(), subst.javaBlock(), subst.getLabels());
    }

    public static LinkedHashSet<Term> replaceAll(Term term, Term grnd,
            LinkedHashSet<Term> subst) {
        LinkedHashSet<Term> ret = new LinkedHashSet<Term>();
        for(Term t: subst) {
            ret.add(replaceAll(term, grnd, t));
        }
        return ret;
    }

}
