package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.RealLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

import java.io.IOException;
import java.math.BigInteger;
import java.util.*;

public class RealHandler implements SMTHandler {

    /** to indicate that an expression holds a value of type Int. */
    public static final SExpr.Type REAL = new SExpr.Type("Real", "r2u", "u2r");
    private static final Name NEGLIT = new Name("neglit");

    private final Map<Operator, String> supportedOperators = new HashMap<>();
    private final Set<Operator> predicateOperators = new HashSet<>();
    private Function realSymbol;
    private Services services;

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets) throws IOException {
        this.services = services;

        RealLDT realLDT = services.getTypeConverter().getRealLDT();

        supportedOperators.clear();
        supportedOperators.put(realLDT.getAdd(), "+");
        supportedOperators.put(realLDT.getMul(), "*");
        supportedOperators.put(realLDT.getSub(), "-");
        supportedOperators.put(realLDT.getDiv(), "/");
        supportedOperators.put(realLDT.getNegation(), "-");
        realSymbol = realLDT.getRealSymbol();
        supportedOperators.put(realSymbol, "");

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
        Operator op = term.op();
        String smtOp = supportedOperators.get(op);
        assert smtOp != null;

        if(op == realSymbol) {
            return handleLiteral(term);
        }

        List<SExpr> children = trans.translate(term.subs(), RealHandler.REAL);
        SExpr.Type resultType;
        if (predicateOperators.contains(op)) {
            resultType = Type.BOOL;
        } else {
            resultType = RealHandler.REAL;
        }

        return new SExpr(smtOp, resultType, children);
    }

    private SExpr handleLiteral(Term term) {
        Term mantTerm = term.sub(0);
        Term expTerm = term.sub(1);

        BigInteger mant = new BigInteger(convertToDecimalString(mantTerm));
        int exp = Integer.parseInt(convertToDecimalString(expTerm));

        SExpr s1;
        if(mant.signum() >= 0) {
            s1 = new SExpr(mant.toString(), REAL);
        } else {
            s1 = new SExpr("-", REAL, mant.negate().toString());
        }

        if (exp == 0) {
            return s1;
        } else if (exp > 0) {
            return new SExpr("*", REAL, s1, new SExpr("1" + "0".repeat(exp)));
        } else {
            return new SExpr("/", REAL, s1, new SExpr("1" + "0".repeat(-exp)));
        }
    }

    private static String convertToDecimalString(Term term) {
        StringBuilder result = new StringBuilder();
        
        if(term.op().name().equals(NEGLIT)) {
            result.append("-");
            term = term.sub(0);
        }

        char symb = term.op().toString().charAt(0);
        while ('0' <= symb && symb <= '9') {
            result.append(symb);
            term = term.sub(0);
            symb = term.op().toString().charAt(0);
        }
        if (symb != '#') {
            throw new RuntimeException("unexpected real constant");
        }
        return result.toString();
    }
}
