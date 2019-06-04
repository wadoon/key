package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.DoubleLDT;
import de.uka.ilkd.key.ldt.FloatLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.smt.NumberTranslation;
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

    private final Map<Operator, SMTTermFloatOp.Op> nonConstOperators = new HashMap<>();
    private final List<Operator> constOperators = new LinkedList<>();
    private FloatLDT floatLDT;
    private DoubleLDT doubleLDT;
    private Services services;

    @Override
    public void init(Services services) throws IOException {
        this.services = services;
        floatLDT = services.getTypeConverter().getFloatLDT();
        doubleLDT = services.getTypeConverter().getDoubleLDT();

        // float literals
        constOperators.add(floatLDT.getFloatSymbol());
        constOperators.add(doubleLDT.getDoubleSymbol());

        // operators with arguments
        nonConstOperators.put(floatLDT.getLessThan(), SMTTermFloatOp.Op.FPLT);
        nonConstOperators.put(floatLDT.getGreaterThan(), SMTTermFloatOp.Op.FPGT);
        nonConstOperators.put(floatLDT.getLessOrEquals(), SMTTermFloatOp.Op.FPLEQ);
        nonConstOperators.put(floatLDT.getGreaterOrEquals(), SMTTermFloatOp.Op.FPGEQ);
        nonConstOperators.put(floatLDT.getEquals(), SMTTermFloatOp.Op.FPEQ);
        nonConstOperators.put(floatLDT.getAddIEEE(), SMTTermFloatOp.Op.FPADD);
        nonConstOperators.put(floatLDT.getSubIEEE(), SMTTermFloatOp.Op.FPSUB);
        nonConstOperators.put(floatLDT.getMulIEEE(), SMTTermFloatOp.Op.FPMUL);
        nonConstOperators.put(floatLDT.getDivIEEE(), SMTTermFloatOp.Op.FPDIV);
        nonConstOperators.put(floatLDT.getJavaUnaryMinus(), SMTTermFloatOp.Op.FPNEG);
        nonConstOperators.put(floatLDT.getAbs(), SMTTermFloatOp.Op.FPABS);
        nonConstOperators.put(floatLDT.getJavaMin(), SMTTermFloatOp.Op.FPMIN);
        nonConstOperators.put(floatLDT.getJavaMax(), SMTTermFloatOp.Op.FPMAX);
        nonConstOperators.put(floatLDT.getIsNaN(), SMTTermFloatOp.Op.FPISNAN);
        nonConstOperators.put(floatLDT.getIsZero(), SMTTermFloatOp.Op.FPISZERO);
        nonConstOperators.put(floatLDT.getIsNormal(), SMTTermFloatOp.Op.FPISNORMAL);
        nonConstOperators.put(floatLDT.getIsSubnormal(), SMTTermFloatOp.Op.FPISSUBNORMAL);
        nonConstOperators.put(floatLDT.getIsInfinite(), SMTTermFloatOp.Op.FPISINFINITE);
        nonConstOperators.put(floatLDT.getIsNegative(), SMTTermFloatOp.Op.FPISNEGATIVE);
        nonConstOperators.put(floatLDT.getIsPositive(), SMTTermFloatOp.Op.FPISPOSITIVE);

        //Double predicates and operations, translated identically to float operations
        nonConstOperators.put(doubleLDT.getLessThan(), SMTTermFloatOp.Op.FPLT);
        nonConstOperators.put(doubleLDT.getGreaterThan(), SMTTermFloatOp.Op.FPGT);
        nonConstOperators.put(doubleLDT.getLessOrEquals(), SMTTermFloatOp.Op.FPLEQ);
        nonConstOperators.put(doubleLDT.getGreaterOrEquals(), SMTTermFloatOp.Op.FPGEQ);
        nonConstOperators.put(doubleLDT.getEquals(), SMTTermFloatOp.Op.FPEQ);
        nonConstOperators.put(doubleLDT.getAddIEEE(), SMTTermFloatOp.Op.FPADD);
        nonConstOperators.put(doubleLDT.getSubIEEE(), SMTTermFloatOp.Op.FPSUB);
        nonConstOperators.put(doubleLDT.getMulIEEE(), SMTTermFloatOp.Op.FPMUL);
        nonConstOperators.put(doubleLDT.getDivIEEE(), SMTTermFloatOp.Op.FPDIV);
        nonConstOperators.put(doubleLDT.getJavaUnaryMinus(), SMTTermFloatOp.Op.FPNEG);
        nonConstOperators.put(doubleLDT.getAbs(), SMTTermFloatOp.Op.FPABS);
        nonConstOperators.put(doubleLDT.getIsNaN(), SMTTermFloatOp.Op.FPISNAN);
        nonConstOperators.put(doubleLDT.getIsZero(), SMTTermFloatOp.Op.FPISZERO);
        nonConstOperators.put(doubleLDT.getIsNormal(), SMTTermFloatOp.Op.FPISNORMAL);
        nonConstOperators.put(doubleLDT.getIsSubnormal(), SMTTermFloatOp.Op.FPISSUBNORMAL);
        nonConstOperators.put(doubleLDT.getIsInfinite(), SMTTermFloatOp.Op.FPISINFINITE);
        nonConstOperators.put(doubleLDT.getIsNegative(), SMTTermFloatOp.Op.FPISNEGATIVE);
        nonConstOperators.put(doubleLDT.getIsPositive(), SMTTermFloatOp.Op.FPISPOSITIVE);
    }

    @Override
    public boolean canHandle(Term term) {
        return nonConstOperators.containsKey(term.op()) || constOperators.contains(term.op());
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        Operator op = term.op();
        if (nonConstOperators.containsKey(op)) {
            SMTTermFloatOp.Op fpop = nonConstOperators.get(op);
            String opName = fpop.getOpName();
            SExpr.Type exprType = fpop.getImageSort().equals(SMTSort.BOOL) ? SExpr.Type.BOOL : SExpr.Type.UNIVERSE;
            ImmutableArray<Term> subs = term.subs();
            List<SExpr> translatedSubs = new LinkedList<>();
            for (Term t : subs) {
                translatedSubs.add(trans.translate(t));
            }
            return new SExpr(opName, exprType, translatedSubs);
        } else if (op.equals(floatLDT.getFloatSymbol())) {
            String fp = NumberTranslation.translateFloatToSMTLIB(term, services);
            fp = fp.substring(1, fp.length() - 1);
            return new SExpr(fp, SExpr.Type.UNIVERSE);
        } else if (op.equals(doubleLDT.getDoubleSymbol())) {
            String dp = NumberTranslation.translateDoubleToSMTLIB(term, services);
            dp = dp.substring(1, dp.length() - 1);
            return new SExpr(dp, SExpr.Type.UNIVERSE);
        }else {
            throw new SMTTranslationException("Error in floating point translation!");
        }

    }
}
