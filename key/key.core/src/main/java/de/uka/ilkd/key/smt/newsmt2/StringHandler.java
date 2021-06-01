package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.CharListLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

import java.io.IOException;
import java.util.*;

public class StringHandler implements SMTHandler {

    @FunctionalInterface
    public interface StringOpHandler {
        SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException;
    }

    public static final Type STRING = new Type("String", "s2u", "u2s");

    private final Map<Operator, StringOpHandler> operators = new HashMap<>();

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets) throws IOException {
        CharListLDT stringLDT = services.getTypeConverter().getCharListLDT();

        masterHandler.addDeclarationsAndAxioms(handlerSnippets);

        masterHandler.addKnownSymbol("sort_string");

        operators.put(stringLDT.getClStartsWith(), (MasterHandler trans, Term term) -> {
            List<SExpr> children = trans.translate(term.subs(), STRING);
            return new SExpr("str.isprefix", Type.BOOL, children);
        });
    }

    @Override
    public boolean canHandle(Operator op) {
        return operators.containsKey(op);
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        return operators.get(term.op()).handle(trans, term);
    }
}
