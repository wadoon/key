package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.DoubleLDT;
import de.uka.ilkd.key.ldt.FloatLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.lang.SMTSort;
import de.uka.ilkd.key.smt.lang.SMTTermFloatOp;
import org.key_project.util.collection.ImmutableArray;

import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class FloatHandler implements SMTHandler {

    private final Map<Operator, SMTTermFloatOp.Op> fpOperators = new HashMap<>();
    private final List<Operator> fpLiterals = new LinkedList<>();
    private FloatLDT floatLDT;
    private DoubleLDT doubleLDT;
    private Services services;

    @Override
    public void init(Services services) throws IOException {
        this.services = services;
        floatLDT = services.getTypeConverter().getFloatLDT();
        doubleLDT = services.getTypeConverter().getDoubleLDT();

        // float literals
        fpLiterals.add(floatLDT.getFloatSymbol());
        fpLiterals.add(doubleLDT.getDoubleSymbol());

        // operators with arguments
        fpOperators.put(floatLDT.getLessThan(), SMTTermFloatOp.Op.FPLT);
        fpOperators.put(floatLDT.getGreaterThan(), SMTTermFloatOp.Op.FPGT);
        fpOperators.put(floatLDT.getLessOrEquals(), SMTTermFloatOp.Op.FPLEQ);
        fpOperators.put(floatLDT.getGreaterOrEquals(), SMTTermFloatOp.Op.FPGEQ);
        fpOperators.put(floatLDT.getEquals(), SMTTermFloatOp.Op.FPEQ);
        fpOperators.put(floatLDT.getAddIEEE(), SMTTermFloatOp.Op.FPADD);
        fpOperators.put(floatLDT.getSubIEEE(), SMTTermFloatOp.Op.FPSUB);
        fpOperators.put(floatLDT.getMulIEEE(), SMTTermFloatOp.Op.FPMUL);
        fpOperators.put(floatLDT.getDivIEEE(), SMTTermFloatOp.Op.FPDIV);
        fpOperators.put(floatLDT.getJavaUnaryMinus(), SMTTermFloatOp.Op.FPNEG);
        fpOperators.put(floatLDT.getAbs(), SMTTermFloatOp.Op.FPABS);
        fpOperators.put(floatLDT.getJavaMin(), SMTTermFloatOp.Op.FPMIN);
        fpOperators.put(floatLDT.getJavaMax(), SMTTermFloatOp.Op.FPMAX);
        fpOperators.put(floatLDT.getIsNaN(), SMTTermFloatOp.Op.FPISNAN);
        fpOperators.put(floatLDT.getIsZero(), SMTTermFloatOp.Op.FPISZERO);
        fpOperators.put(floatLDT.getIsNormal(), SMTTermFloatOp.Op.FPISNORMAL);
        fpOperators.put(floatLDT.getIsSubnormal(), SMTTermFloatOp.Op.FPISSUBNORMAL);
        fpOperators.put(floatLDT.getIsInfinite(), SMTTermFloatOp.Op.FPISINFINITE);
        fpOperators.put(floatLDT.getIsNegative(), SMTTermFloatOp.Op.FPISNEGATIVE);
        fpOperators.put(floatLDT.getIsPositive(), SMTTermFloatOp.Op.FPISPOSITIVE);

        //Double predicates and operations, translated identically to float operations
        fpOperators.put(doubleLDT.getLessThan(), SMTTermFloatOp.Op.FPLT);
        fpOperators.put(doubleLDT.getGreaterThan(), SMTTermFloatOp.Op.FPGT);
        fpOperators.put(doubleLDT.getLessOrEquals(), SMTTermFloatOp.Op.FPLEQ);
        fpOperators.put(doubleLDT.getGreaterOrEquals(), SMTTermFloatOp.Op.FPGEQ);
        fpOperators.put(doubleLDT.getEquals(), SMTTermFloatOp.Op.FPEQ);
        fpOperators.put(doubleLDT.getAddIEEE(), SMTTermFloatOp.Op.FPADD);
        fpOperators.put(doubleLDT.getSubIEEE(), SMTTermFloatOp.Op.FPSUB);
        fpOperators.put(doubleLDT.getMulIEEE(), SMTTermFloatOp.Op.FPMUL);
        fpOperators.put(doubleLDT.getDivIEEE(), SMTTermFloatOp.Op.FPDIV);
        fpOperators.put(doubleLDT.getJavaUnaryMinus(), SMTTermFloatOp.Op.FPNEG);
        fpOperators.put(doubleLDT.getAbs(), SMTTermFloatOp.Op.FPABS);
        fpOperators.put(doubleLDT.getIsNaN(), SMTTermFloatOp.Op.FPISNAN);
        fpOperators.put(doubleLDT.getIsZero(), SMTTermFloatOp.Op.FPISZERO);
        fpOperators.put(doubleLDT.getIsNormal(), SMTTermFloatOp.Op.FPISNORMAL);
        fpOperators.put(doubleLDT.getIsSubnormal(), SMTTermFloatOp.Op.FPISSUBNORMAL);
        fpOperators.put(doubleLDT.getIsInfinite(), SMTTermFloatOp.Op.FPISINFINITE);
        fpOperators.put(doubleLDT.getIsNegative(), SMTTermFloatOp.Op.FPISNEGATIVE);
        fpOperators.put(doubleLDT.getIsPositive(), SMTTermFloatOp.Op.FPISPOSITIVE);
    }

    @Override
    public boolean canHandle(Term term) {
        return fpOperators.containsKey(term.op()) || fpLiterals.contains(term.op());
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        Operator op = term.op();
        if (fpOperators.containsKey(op)) {
            SMTTermFloatOp.Op fpop = fpOperators.get(op);
            String opName = fpop.getOpName();
            SExpr.Type exprType = fpop.getImageSort().equals(SMTSort.BOOL) ? SExpr.Type.BOOL : SExpr.Type.FLOAT;
            ImmutableArray<Term> subs = term.subs();
            List<SExpr> translatedSubs = new LinkedList<>();
            for (Term t : subs) {
                translatedSubs.add(trans.translate(t));
            }
            return new SExpr(opName, exprType, translatedSubs);
        } // else if ... else if ...
          else {
            throw new SMTTranslationException("Error in floating point translation!");
        }
    }
}
