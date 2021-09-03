package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.DoubleLDT;
import de.uka.ilkd.key.ldt.FloatLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.smt.NumberTranslation;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.lang.*;
import de.uka.ilkd.key.smt.lang.SMTTermFloatOp.Op;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;
import org.key_project.util.collection.ImmutableArray;

import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class FloatHandler implements SMTHandler {

    private final Map<Operator, SMTTermFloatOp.Op> fpOperators = new HashMap<>();
    private final Map<Operator, SMTTermFloatOp.Op> mathOperators = new HashMap<>();
    private final List<Operator> fpLiterals = new LinkedList<>();
    private FloatLDT floatLDT;
    private DoubleLDT doubleLDT;
    private Services services;
    private boolean disableSqrtAxiomatizing;

    @Override
    public void init(Services services) throws IOException {

        this.services = services;
        floatLDT = services.getTypeConverter().getFloatLDT();
        doubleLDT = services.getTypeConverter().getDoubleLDT();
        disableSqrtAxiomatizing = services.getProof().getSettings().getSMTSettings().disableSqrtAxiomatizing;

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
        fpOperators.put(floatLDT.getIsPositive(), SMTTermFloatOp.Op.FPISPOSITIVE);
        fpOperators.put(floatLDT.getJavaUnaryMinus(), SMTTermFloatOp.Op.FPNEG);
        fpOperators.put(floatLDT.getAbs(), SMTTermFloatOp.Op.FPABS);
        fpOperators.put(floatLDT.getFloor(), new Op("float_floor", SMTSort.FLOAT, SMTSort.FLOAT));
        fpOperators.put(floatLDT.getJavaMin(), SMTTermFloatOp.Op.FPMIN);
        fpOperators.put(floatLDT.getJavaMax(), SMTTermFloatOp.Op.FPMAX);
        fpOperators.put(floatLDT.getIsNaN(), SMTTermFloatOp.Op.FPISNAN);
        fpOperators.put(floatLDT.getIsZero(), SMTTermFloatOp.Op.FPISZERO);
        fpOperators.put(floatLDT.getIsNormal(), SMTTermFloatOp.Op.FPISNORMAL);
        fpOperators.put(floatLDT.getIsSubnormal(), SMTTermFloatOp.Op.FPISSUBNORMAL);
        fpOperators.put(floatLDT.getIsInfinite(), SMTTermFloatOp.Op.FPISINFINITE);
        fpOperators.put(floatLDT.getIsNegative(), SMTTermFloatOp.Op.FPISNEGATIVE);
        fpOperators.put(floatLDT.getIsPositive(), SMTTermFloatOp.Op.FPISPOSITIVE);
        fpOperators.put(floatLDT.getJavaMod(), SMTTermFloatOp.Op.FPMOD);

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
        fpOperators.put(doubleLDT.getJavaMod(), SMTTermFloatOp.Op.FPMOD);

        mathOperators.put(doubleLDT.getSinDouble(), SMTTermFloatOp.Op.SINDOUBLE);
        mathOperators.put(doubleLDT.getCosDouble(), SMTTermFloatOp.Op.COSDOUBLE);
        mathOperators.put(doubleLDT.getAcosDouble(), SMTTermFloatOp.Op.ACOSDOUBLE);
        mathOperators.put(doubleLDT.getAsinDouble(), SMTTermFloatOp.Op.ASINDOUBLE);
        mathOperators.put(doubleLDT.getTanDouble(), SMTTermFloatOp.Op.TANDOUBLE);
        mathOperators.put(doubleLDT.getAtan2Double(), SMTTermFloatOp.Op.ATAN2DOUBLE);
        mathOperators.put(doubleLDT.getSqrtDouble(), SMTTermFloatOp.Op.SQRTDOUBLE);
        mathOperators.put(doubleLDT.getPowDouble(), SMTTermFloatOp.Op.POWDOUBLE);
        mathOperators.put(doubleLDT.getExpDouble(), SMTTermFloatOp.Op.EXPDOUBLE);
        mathOperators.put(doubleLDT.getAtanDouble(), SMTTermFloatOp.Op.ATANDOUBLE);
        mathOperators.put(doubleLDT.getCbrtDouble(), SMTTermFloatOp.Op.CBRTDOUBLE);
        mathOperators.put(doubleLDT.getCoshDouble(), SMTTermFloatOp.Op.COSHDOUBLE);
        mathOperators.put(doubleLDT.getExpm1Double(), SMTTermFloatOp.Op.EXPM1DOUBLE);
        mathOperators.put(doubleLDT.getHypotDouble(), SMTTermFloatOp.Op.HYPOTDOUBLE);
        mathOperators.put(doubleLDT.getLogDouble(), SMTTermFloatOp.Op.LOGDOUBLE);
        mathOperators.put(doubleLDT.getLog10Double(), SMTTermFloatOp.Op.LOG10DOUBLE);
        mathOperators.put(doubleLDT.getLog1pDouble(), SMTTermFloatOp.Op.LOG1PDOUBLE);
        mathOperators.put(doubleLDT.getSinhDouble(), SMTTermFloatOp.Op.SINHDOUBLE);
        mathOperators.put(doubleLDT.getTanhDouble(), SMTTermFloatOp.Op.TANHDOUBLE);
    }

    @Override
    public boolean canHandle(Term term) {

        Operator op = term.op();

        if (fpOperators.containsKey(op) ||mathOperators.containsKey(op) || fpLiterals.contains(op) || op == doubleLDT.getRoundingModeRNE()
            || op == doubleLDT.getRoundingModeRTN() || op == doubleLDT.getRoundingModeRTP())

            return true;

        return false;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {

        trans.addFromSnippets("float");
        trans.addFromSnippets("double");

        Operator op = term.op();
        if (fpOperators.containsKey(op) || mathOperators.containsKey(op)) {
            SMTTermFloatOp.Op fpop;
            if(fpOperators.containsKey(op)) {
                fpop = fpOperators.get(op);
            }else {
                fpop = mathOperators.get(op);
                if(!disableSqrtAxiomatizing || fpop != SMTTermFloatOp.Op.SQRTDOUBLE){
                    trans.addFromSnippets(fpop.getOpName());
                }else {
                    fpop = SMTTermFloatOp.Op.FPSQRT;
                }
            }
            String opName = fpop.getOpName();
            SExpr.Type exprType;
            if (fpop.getImageSort().equals(SMTSort.BOOL)) exprType = SExpr.Type.BOOL;
            else if (fpop.getImageSort().equals(SMTSort.DOUBLE)) exprType = SExpr.Type.DOUBLE;
            else exprType = SExpr.Type.FLOAT;

            ImmutableArray<Term> subs = term.subs();

            ///
            /// DIRTIEST HACK EVER
            ///
            // No function from the double family ever returns float.
            if(exprType == Type.FLOAT && subs.last().sort().name().toString().equals("double")) {
                exprType = Type.DOUBLE;
            }

            List<SExpr> translatedSubs = new LinkedList<>();

            for (Term t : subs) {

                Operator subOp = t.op();
                String termType = t.sort().toString();

                if (subOp instanceof ProgramVariable ||
                        ((Function) subOp).isSkolemConstant() ||
                        services.getTypeConverter().getHeapLDT().isSelectOp(subOp) ||
                        ((Function) subOp).sort().equals(floatLDT.targetSort())) {


                    if (termType.equals("float"))
                        translatedSubs.add(trans.translate(t, SExpr.Type.FLOAT));
                    else if (termType.equals("double"))
                        translatedSubs.add(trans.translate(t, SExpr.Type.DOUBLE));

                } else
                    translatedSubs.add(trans.translate(t));
            }
            return new SExpr(opName, exprType, translatedSubs);

        } else if (fpLiterals.contains(op)) {

            String lit = op.name().toString();
            if (lit.equals("DFP")) {
                return new SExpr(NumberTranslation.translateDoubleToSMTLIB(term, services), SExpr.Type.DOUBLE);
            } else { // lit.equals("FP")
                return new SExpr(NumberTranslation.translateFloatToSMTLIB(term, services), SExpr.Type.FLOAT);
            }

        } else if (op == doubleLDT.getRoundingModeRNE()) {
            return new SExpr(SMTTermConst.FP_RNE.toString());

        } else if (op == doubleLDT.getRoundingModeRTN()) {
            return new SExpr(SMTTermConst.FP_RTN.toString());

        } else if (op == doubleLDT.getRoundingModeRTP()) {
            return new SExpr(SMTTermConst.FP_RTP.toString());

        } else {
            throw new SMTTranslationException("Error in floating point translation!");
        }
    }
}
