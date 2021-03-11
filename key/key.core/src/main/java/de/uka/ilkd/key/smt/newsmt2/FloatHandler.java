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
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;
import org.key_project.util.collection.ImmutableArray;

import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Properties;

public class FloatHandler implements SMTHandler {

    public static final Type FLOAT = new Type("Float", "f2u", "u2f");
    public static final Type DOUBLE = new Type("Double", "d2u", "u2d");

    private final Map<Operator, SMTTermFloatOp.Op> fpOperators = new HashMap<>();
    private final Map<Operator, SMTTermFloatOp.Op> mathOperators = new HashMap<>();
    private final List<Operator> fpLiterals = new LinkedList<>();
    private FloatLDT floatLDT;
    private DoubleLDT doubleLDT;
    private Services services;

    // TODO Take this from the smt settings (once available)
    private boolean disableSqrtAxiomatizing;
    private Properties snippets;

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets) throws IOException {

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

        masterHandler.addDeclarationsAndAxioms(handlerSnippets);
    }

    @Override
    public boolean canHandle(Operator op) {

        return fpOperators.containsKey(op) || mathOperators.containsKey(op)
                || fpLiterals.contains(op);
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {

        trans.introduceSymbol("float");
        trans.introduceSymbol("double");

        Operator op = term.op();
        if (fpOperators.containsKey(op) || mathOperators.containsKey(op)) {
            SMTTermFloatOp.Op fpop;
            if(fpOperators.containsKey(op)) {
                fpop = fpOperators.get(op);
            }else {
                fpop = mathOperators.get(op);
                if(disableSqrtAxiomatizing && fpop == SMTTermFloatOp.Op.SQRTDOUBLE){
                    fpop = SMTTermFloatOp.Op.FPSQRT;
                } else {
                    trans.introduceSymbol(fpop.getOpName());
                }
            }
            String opName = fpop.getOpName();
            SExpr.Type exprType;
            if (fpop.getImageSort().equals(SMTSort.BOOL)) exprType = SExpr.Type.BOOL;
            else if (fpop.getImageSort().equals(SMTSort.DOUBLE)) exprType = DOUBLE;
            else exprType = FLOAT;

            ImmutableArray<Term> subs = term.subs();

            ///
            /// DIRTIEST HACK EVER
            ///
            // No function from the double family ever returns float.
//            if(exprType == FLOAT && subs.last().sort().name().toString().equals("double")) {
//                exprType = DOUBLE;
//            }

            List<SExpr> translatedSubs = new LinkedList<>();

            int arg = 0;
            List<SMTSort> domain = fpop.getDomainSorts();
            if(!domain.isEmpty() && domain.get(arg).equals(SMTTermFloatOp.ROUNDMODESORT)) {
                arg++;
                translatedSubs.add(new SExpr("RNE"));
            }

            for (Term t : subs) {
                SMTSort expected = domain.get(arg);
                if (expected.equals(SMTSort.DOUBLE))
                    translatedSubs.add(trans.translate(t, DOUBLE));
                else if (expected.equals(SMTSort.FLOAT))
                    translatedSubs.add(trans.translate(t, FLOAT));
                else
                    throw new SMTTranslationException("Unexpected type " + expected);
            }
            
            return new SExpr(opName, exprType, translatedSubs);

        } else if (fpLiterals.contains(op)) {
            if (op == services.getTypeConverter().getDoubleLDT().getDoubleSymbol()) {
                return NumberTranslation.translateDoubleToSMTLIB(term, services);
            } else {
                return NumberTranslation.translateFloatToSMTLIB(term, services);
            }

        } else {
            throw new SMTTranslationException("Error in floating point translation!");
        }
    }
}
