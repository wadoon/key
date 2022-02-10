package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.RealLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

import java.io.IOException;
import java.util.*;

public class RealHandler implements SMTHandler {

    /** to indicate that an expression holds a value of type Int. */
    public static final SExpr.Type REAL = new SExpr.Type("Real", "r2u", "u2r");

    private final Map<Operator, String> supportedOperators = new HashMap<>();
    private final Set<Operator> predicateOperators = new HashSet<>();

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets) throws IOException {

        supportedOperators.clear();
        RealLDT realLDT = services.getTypeConverter().getRealLDT();

        supportedOperators.put(realLDT.getAdd(), "+");
        supportedOperators.put(realLDT.getMul(), "*");
        supportedOperators.put(realLDT.getSub(), "-");
        supportedOperators.put(realLDT.getDiv(), "/");
        supportedOperators.put(realLDT.getNegation(), "-");
        supportedOperators.put(realLDT.getRealSymbol(), "");

        supportedOperators.put(realLDT.getLessOrEquals(), "<=");
        predicateOperators.add(realLDT.getLessOrEquals());
        supportedOperators.put(realLDT.getLessThan(), "<");
        predicateOperators.add(realLDT.getLessThan());
        supportedOperators.put(realLDT.getGreaterOrEquals(), ">=");
        predicateOperators.add(realLDT.getGreaterOrEquals());
        supportedOperators.put(realLDT.getGreaterThan(), ">");
        predicateOperators.add(realLDT.getGreaterThan());

        masterHandler.addDeclarationsAndAxioms(handlerSnippets);

        // sort_real is defined here, declare it as already defined
        masterHandler.addKnownSymbol("sort_real");
    }

    @Override
    public boolean canHandle(Operator op) {
        return supportedOperators.containsKey(op);
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        List<SExpr> children = trans.translate(term.subs(), RealHandler.REAL);
        Operator op = term.op();
        String smtOp = supportedOperators.get(op);
        assert smtOp != null;

        SExpr.Type resultType;
        if (predicateOperators.contains(op)) {
            resultType = Type.BOOL;
        } else {
            resultType = RealHandler.REAL;
        }

        return new SExpr(smtOp, resultType, children);
    }
}
