package de.uka.ilkd.key.smt.newsmt2;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class QuantifierHandler implements SMTHandler {

    private Services services;

    @Override
    public void init(Services services) {
        this.services = services;
    }

    @Override
    public boolean canHandle(Term term) {
        Operator op = term.op();
        return op == Quantifier.ALL || op == Quantifier.EX;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {

        if (!(services.getProof().getSettings().getSMTSettings().enableQuantifiers)) {
            return handleWithoutQuantifiers(trans, term);
        }

        SExpr matrix = trans.translate(term.sub(0), Type.BOOL);
        List<SExpr> vars = new ArrayList<>();
        for(QuantifiableVariable bv : term.boundVars()) {
            vars.add(new SExpr(LogicalVariableHandler.VAR_PREFIX + bv.name(), Type.NONE, "U"));
        }

        String smtOp;
        Operator op = term.op();
        if(op == Quantifier.ALL) {
            smtOp = "forall";
        } else if(op == Quantifier.EX) {
            smtOp = "exists";
        } else {
            throw new SMTTranslationException("Unknown quantifier " + op);
        }

        return new SExpr(smtOp, Type.BOOL, new SExpr(vars), matrix);

    }

    private SExpr handleWithoutQuantifiers(MasterHandler trans, Term term) {
        List<SExpr> vars = new ArrayList<>();
        for(QuantifiableVariable bv : term.boundVars()) {
            trans.addDeclaration(new SExpr("declare-const", Type.NONE, LogicalVariableHandler.VAR_PREFIX + bv.name(), "U"));
        }
        return trans.translate(term.sub(0), Type.BOOL);
    }

}
