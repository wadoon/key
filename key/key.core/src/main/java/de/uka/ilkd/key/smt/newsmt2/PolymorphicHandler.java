package de.uka.ilkd.key.smt.newsmt2;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class PolymorphicHandler implements SMTHandler {

    @Override
    public void init(Services services) {
        // nothing to be done
    }

    @Override
    public boolean canHandle(Term term) {
        Operator op = term.op();
        return op == Equality.EQUALS || op == IfThenElse.IF_THEN_ELSE;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        Operator op = term.op();
        if(op == Equality.EQUALS) {
            List<SExpr> children = trans.translate(term.subs());
            children.set(0, trans.coerce(children.get(0), Type.UNIVERSE));
            children.set(1, trans.coerce(children.get(1), Type.UNIVERSE));
            return new SExpr("=", Type.BOOL, children);
        }

        if(op == IfThenElse.IF_THEN_ELSE) {
            List<SExpr> children = trans.translate(term.subs());
            children.set(0, trans.coerce(children.get(0), Type.BOOL));
            children.set(1, trans.coerce(children.get(1), Type.UNIVERSE));
            children.set(2, trans.coerce(children.get(2), Type.UNIVERSE));
            return new SExpr("ite", Type.UNIVERSE, children);
        }

        throw new Error("unreachable");
    }

}