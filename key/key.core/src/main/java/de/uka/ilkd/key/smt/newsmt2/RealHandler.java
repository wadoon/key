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

        supportedOperators.put(realLDT.getRAdd(), "+");
        supportedOperators.put(realLDT.getrMul(), "*");
        supportedOperators.put(realLDT.getRSub(), "-");
        supportedOperators.put(realLDT.getrDiv(), "/");
        supportedOperators.put(realLDT.getRNeg(), "-");
        supportedOperators.put(realLDT.getRealSymbol(), "");

        supportedOperators.put(realLDT.getRlgt(), "<=");
        predicateOperators.add(realLDT.getRlgt());
        supportedOperators.put(realLDT.getRlt(), "<");
        predicateOperators.add(realLDT.getRlt());
        supportedOperators.put(realLDT.getRge(), ">=");
        predicateOperators.add(realLDT.getRge());
        supportedOperators.put(realLDT.getRgt(), ">");
        predicateOperators.add(realLDT.getRgt());

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
