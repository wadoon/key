package de.uka.ilkd.key.strategy.normalization.simple;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.strategy.termgenerator.TermGenerator;

public class SmallClauseNormalForm {

    private final TermBuilder tb;
    private final Term falseT;
    private final Term trueT;

    public SmallClauseNormalForm(TermBuilder tb) {
        this.tb = tb;
        falseT = tb.ff();
        trueT = tb.tt();
    }

    public Term toSCNF(Term term) {
        return simplify(term).getTerm();
    }
    
    private NormResult simplify(Term term) {
        if(isAnd(term)) {
            Term a = term.sub(0);
            Term b = term.sub(1);
            if(eq(a, b)) return simplify(a);
            if(negEq(a, b)) return new NormResult(falseT, true);
            if(a.equals(falseT) || b.equals(falseT)) return new NormResult(falseT, true);
            if(a.equals(trueT)) return simplify(b);
            if(b.equals(trueT)) return simplify(a);
        }
        if(isOr(term)) {
            Term a = term.sub(0);
            Term b = term.sub(1);
            if(eq(a, b)) return simplify(a);
            if(negEq(a, b)) return new NormResult(trueT, true);
            if(a.equals(trueT) || b.equals(trueT)) return new NormResult(trueT, true);
            if(a.equals(falseT)) return simplify(b);
            if(b.equals(falseT)) return simplify(a);
        }
        if(isImp(term)) {
            Term a = term.sub(0);
            Term b = term.sub(1);
            if(eq(a, b)) return new NormResult(trueT, true);
            if(b.equals(trueT)) return new NormResult(trueT, true);
            if(a.equals(falseT)) return new NormResult(trueT, true);
            if(a.equals(trueT)) simplify(b);
            if(b.equals(falseT)) simplify(tb.not(a));
        }
        if(isEquiv(term)) {
            Term a = term.sub(0);
            Term b = term.sub(1);
            if(eq(a, b)) return new NormResult(trueT, true);
            if(a.equals(trueT)) return simplify(b);
            if(b.equals(trueT)) return simplify(a);
            if(a.equals(falseT)) return simplify(tb.not(b));
            if(b.equals(falseT)) return simplify(tb.not(a));
        }
        if(isIfThenElse(term)) {
            Term a = term.sub(0);
            Term b = term.sub(1);
            Term c = term.sub(3);
            if(a.equals(trueT)) return simplify(b);
            if(a.equals(falseT)) return simplify(c);
        }
        return miniscope(term);
    }

    private NormResult simplify(NormResult result) {
        Term term = result.getTerm();
        if(isAnd(term)) {
            Term a = term.sub(0);
            Term b = term.sub(1);
            if(eq(a, b)) return new NormResult(a, true);
            if(negEq(a, b)) return new NormResult(falseT, true);
            if(a.equals(falseT) || b.equals(falseT)) return new NormResult(falseT, true);
            if(a.equals(trueT)) return new NormResult(b, true);
            if(b.equals(trueT)) return new NormResult(a, true);
        }
        if(isOr(term)) {
            Term a = term.sub(0);
            Term b = term.sub(1);
            if(eq(a, b)) return new NormResult(a, true);
            if(negEq(a, b)) return new NormResult(trueT, true);
            if(a.equals(trueT) || b.equals(trueT)) return new NormResult(trueT, true);
            if(a.equals(falseT)) return new NormResult(b, true);
            if(b.equals(falseT)) new NormResult(a, true);
        }
        return miniscope(result);
    }

    private NormResult miniscope(Term term) {
        if(!SimpleFormulaNormalization.isMiniscoping()) nnf(term);
        if(isQuantifier(term)) {
            Term qf = term.sub(0);
            QuantifiableVariable qv = term.varsBoundHere(0).get(0);
            if(term.op() == Quantifier.EX) {
                if(isAnd(qf) && !qf.sub(0).freeVars().contains(qv))
                    return simplify(simplify(qf.sub(0)).and(simplify(simplify(qf.sub(1)).ex(qv))));
                if(isAnd(qf) && !qf.sub(1).freeVars().contains(qv))
                    return simplify(simplify(simplify(qf.sub(0)).ex(qv)).and(simplify(qf.sub(1))));
                if(isOr(qf) && !qf.sub(0).freeVars().contains(qv))
                    return simplify(simplify(qf.sub(0)).or(simplify(simplify(qf.sub(1)).ex(qv))));
                if(isOr(qf) && !qf.sub(1).freeVars().contains(qv))
                    return simplify(simplify(simplify(qf.sub(0)).ex(qv)).or(simplify(qf.sub(1))));
            }
            if(term.op() == Quantifier.ALL) {
                if(isAnd(qf) && !qf.sub(0).freeVars().contains(qv))
                    return simplify(simplify(qf.sub(0)).and(simplify(simplify(qf.sub(1)).all(qv))));
                if(isAnd(qf) && !qf.sub(1).freeVars().contains(qv))
                    return simplify(simplify(simplify(qf.sub(0)).all(qv)).and(simplify(qf.sub(1))));
                if(isOr(qf) && !qf.sub(0).freeVars().contains(qv))
                    return simplify(simplify(qf.sub(0)).or(simplify(simplify(qf.sub(1)).all(qv))));
                if(isOr(qf) && !qf.sub(1).freeVars().contains(qv))
                    return simplify(simplify(simplify(qf.sub(0)).all(qv)).or(simplify(qf.sub(1))));
            }
        }
        return nnf(term);
    }

    private NormResult miniscope(NormResult result) {
        if(!SimpleFormulaNormalization.isMiniscoping()) nnf(result);
        Term term = result.getTerm();
        if(isQuantifier(term)) {
            Term qf = term.sub(0);
            QuantifiableVariable qv = term.varsBoundHere(0).get(0);
            if(term.op() == Quantifier.EX) {
                if(isAnd(qf) && !qf.sub(0).freeVars().contains(qv))
                    return simplify(new NormResult(qf.sub(0)).and(simplify(new NormResult(tb.ex(qv, qf.sub(1))))));
                if(isAnd(qf) && !qf.sub(1).freeVars().contains(qv))
                    return simplify(simplify(new NormResult(tb.ex(qv, qf.sub(0)))).and(new NormResult(qf.sub(1))));
                if(isOr(qf) && !qf.sub(0).freeVars().contains(qv))
                    return simplify(new NormResult(qf.sub(0)).or(simplify(new NormResult(tb.ex(qv, qf.sub(1))))));
                if(isOr(qf) && !qf.sub(1).freeVars().contains(qv))
                    return simplify(simplify(new NormResult(tb.ex(qv, qf.sub(0)))).or(new NormResult(qf.sub(1))));
            }
            if(term.op() == Quantifier.ALL) {
                if(isAnd(qf) && !qf.sub(0).freeVars().contains(qv))
                    return simplify(new NormResult(qf.sub(0)).and(simplify(new NormResult(tb.all(qv, qf.sub(1))))));
                if(isAnd(qf) && !qf.sub(1).freeVars().contains(qv))
                    return simplify(simplify(new NormResult(tb.all(qv, qf.sub(0)))).and(new NormResult(qf.sub(1))));
                if(isOr(qf) && !qf.sub(0).freeVars().contains(qv))
                    return simplify(new NormResult(qf.sub(0)).or(simplify(new NormResult(tb.all(qv, qf.sub(1))))));
                if(isOr(qf) && !qf.sub(1).freeVars().contains(qv))
                    return simplify(simplify(new NormResult(tb.all(qv, qf.sub(0)))).or(new NormResult(qf.sub(1))));
            }
        }
        return nnf(result);
    }

    private NormResult nnf(Term term) {
        if(isImp(term))
            return simplify(simplify(tb.not(term.sub(0))).or(simplify(term.sub(1))));
        if(isEquiv(term)) {
            return simplify(simplify(simplify(tb.not(term.sub(0))).or(simplify(term.sub(1)))).and(simplify(simplify(term.sub(0)).or(simplify(tb.not(term.sub(1)))))));
        }
        if(isNot(term)) {
            Term neg = term.sub(0);
            if(isNot(neg))
                return simplify(neg.sub(0));
            if(isAnd(neg))
                return simplify(simplify(tb.not(neg.sub(0))).or(simplify(tb.not(neg.sub(1)))));
            if(isOr(neg))
                return simplify(simplify(tb.not(neg.sub(0))).and(simplify(tb.not(neg.sub(1)))));
            if(isImp(neg))
                return simplify(simplify(neg.sub(0)).and(simplify(tb.not(neg.sub(1)))));
            if(isEquiv(neg))
                return simplify(simplify(simplify(neg.sub(0)).and(simplify(tb.not(neg.sub(1))))).or(simplify(simplify(tb.not(neg.sub(0))).or(simplify(neg.sub(1))))));
            if(isIfThenElse(neg))
                return simplify(simplify(simplify(neg.sub(0)).and(simplify(tb.not(neg.sub(1))))).or(simplify(simplify(tb.not(neg.sub(0))).or(simplify(tb.not(neg.sub(2)))))));
            if(isQuantifier(neg)) {
                QuantifiableVariable qv = neg.varsBoundHere(0).get(0);
                if(neg.op() == Quantifier.EX)
                    return simplify(simplify(tb.not(neg.sub(0))).all(qv));
                if(neg.op() == Quantifier.ALL)
                    return simplify(simplify(tb.not(neg.sub(0))).ex(qv));
            }
        }
        if(isIfThenElse(term))
            return simplify(simplify(simplify(tb.not(term.sub(0))).or(simplify(term.sub(1)))).and(simplify(simplify(term.sub(0)).or(simplify(tb.not(term.sub(2)))))));
        if(isQuantifier(term)) {
            QuantifiableVariable qv = term.varsBoundHere(0).get(0);
            if(term.op() == Quantifier.ALL)
                return simplify(simplify(term.sub(0)).all(qv));
            if(term.op() == Quantifier.EX)
                return simplify(simplify(term.sub(0)).ex(qv));
        }
        if(isOr(term))
            return simplify(simplify(term.sub(0)).or(simplify(term.sub(1))));
        if(isAnd(term))
            return simplify(simplify(term.sub(0)).and(simplify(term.sub(1))));
        // nothing else matches, this is a literal.
        return new NormResult(term);
    }

    private NormResult nnf(NormResult result) {
        Term term = result.getTerm();
        if(isNot(term)) {
            Term neg = term.sub(0);
            if(isNot(neg))
                return new NormResult(term, true);
            if(isAnd(neg))
                return simplify(simplify(new NormResult(tb.not(neg.sub(0)))).and(simplify(new NormResult(tb.not(neg.sub(1))))));
            if(isOr(neg))
                return simplify(simplify(new NormResult(tb.not(neg.sub(0)))).or(simplify(new NormResult(tb.not(neg.sub(1))))));
            if(isQuantifier(neg)) {
                QuantifiableVariable qv = neg.varsBoundHere(0).get(0);
                if(neg.op() == Quantifier.EX)
                    return simplify(simplify(new NormResult(tb.not(neg.sub(0)))).all(qv));
                if(neg.op() == Quantifier.ALL)
                    return simplify(simplify(new NormResult(tb.not(neg.sub(0)))).ex(qv));
            }
        }
        return result;
    }


    private NormResult and(NormResult a, NormResult b) {
        return simplify(a.and(b));
    }

    private NormResult or(NormResult a, NormResult b) {
        return simplify(a.or(b));
    }


    private static boolean negEq(Term a, Term b) {
        return (isNot(a) && a.sub(0).equals(b)) || (isNot(b) && b.sub(0).equals(a));
    }

    private static boolean eq(Term a, Term b) {
        return a.equals(b);
    }

    private static boolean isAnd(Term term) {
        return term.op() == Junctor.AND;
    }

    private static boolean isOr(Term term) {
        return term.op() == Junctor.OR;
    }

    private static boolean isNot(Term term) {
        return term.op() == Junctor.NOT;
    }

    private static boolean isImp(Term term) {
        return term.op() == Junctor.IMP;
    }

    private static boolean isEquiv(Term term) {
        return term.op() == Equality.EQV;
    }

    private static boolean isIfThenElse(Term term) {
        return term.op() instanceof IfThenElse;
    }

    private static boolean isQuantifier(Term term) {
        return term.op() instanceof Quantifier;
    }

//    private static BinaryMatcher simplifyAndMatcher = new BinaryMatcher() {
//        @Override
//        public Rule match(Term a, Term b) {
//            // fsn-11
//            if(a.equals(falseT) || term.sub(1).equals(falseT))
//                return falseT;
//            // fsn-3
//            if(negEq(term.sub(0), term.sub(1)))
//                return falseT;
//            // fsn-1
//            if(term.sub(0).equals(term.sub(1)))
//                return simplify(term.sub(0));
//            if(term.sub(0).equals(trueT))
//                return simplify(term.sub(1));
//            if(term.sub(1).equals(trueT))
//                return simplify(term.sub(0));
//        }
//    };

    private class NormResult {
        private Term term;
        private boolean modified;

        public NormResult(Term term) {
            this.term = term;
            this.modified = false;
        }

        public NormResult(Term term, boolean modified) {
            this.term = term;
            this.modified = modified;
        }

        public boolean isModified() {
            return this.modified;
        }

        public Term getTerm() {
            return term;
        }

        public NormResult neg() {
            this.modified = true;
            this.term = tb.not(term);
            return this;
        }

        public NormResult neg(Term orig) {
            if(modified) {
                this.term = tb.not(this.term);
            }else {
                this.term = orig;
            }
            return this;
        }

        public NormResult and(NormResult other) {
            this.modified = true;
            this.term = tb.and(this.term, other.term);
            return this;
        }

        public NormResult and(Term orig, NormResult other) {
            if(this.modified || other.modified) {
                this.modified = true;
                this.term = tb.and(this.term, other.term);
            }else {
                this.term = orig;
            }
            return this;
        }

        public NormResult or(NormResult other) {
            this.modified = true;
            this.term = tb.or(this.term, other.term);
            return this;
        }

        public NormResult or(Term orig, NormResult other) {
            if(this.modified || other.modified) {
                this.modified = true;
                this.term = tb.or(this.term, other.term);
            }else {
                this.term = orig;
            }
            return this;
        }

        public NormResult ex(QuantifiableVariable qv) {
            this.modified = true;
            this.term = tb.ex(qv, term);
            return this;
        }

        public NormResult ex(Term orig, QuantifiableVariable qv) {
            if(this.modified) {
                this.term = tb.ex(qv, term);
            }else {
                this.term = orig;
            }
            return this;
        }

        public NormResult all(QuantifiableVariable qv) {
            this.modified = true;
            this.term = tb.all(qv, term);
            return this;
        }

        public NormResult all(Term orig, QuantifiableVariable qv) {
            if(this.modified) {
                this.term = tb.all(qv, term);
            }else {
                this.term = orig;
            }
            return this;
        }
    }

}
