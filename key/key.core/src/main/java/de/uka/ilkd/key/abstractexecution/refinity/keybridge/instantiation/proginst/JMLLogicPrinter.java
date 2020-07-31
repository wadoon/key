// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2020 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.proginst;

import java.io.IOException;
import java.util.Arrays;
import java.util.Map;

import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.pp.FieldPrinter;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.Notation;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import de.uka.ilkd.key.speclang.jml.translation.JMLTranslator;
import de.uka.ilkd.key.speclang.jml.translation.JMLTranslator.JMLKeyWord;

/**
 * Specialized {@link LogicPrinter} for printing JavaDL terms in JML syntax.
 * 
 * @author Dominic Steinhoefel
 */
public final class JMLLogicPrinter extends SequentViewLogicPrinter {
    /**
     * @param prgPrinter
     * @param notationInfo
     * @param services
     * @param visibleTermLabels
     */
    JMLLogicPrinter(ProgramPrinter prgPrinter, NotationInfo notationInfo, Services services,
            VisibleTermLabels visibleTermLabels) {
        super(prgPrinter, notationInfo, services, visibleTermLabels);
    }

    @Override
    public void printFunctionTerm(Term t) throws IOException {
        if (notationInfo.isPrettySyntax() && services != null
                && FieldPrinter.isJavaFieldConstant(t, getHeapLDT(), services)
                && getNotationInfo().isHidePackagePrefix()
                || t.op() instanceof SortDependingFunction) {
            super.printFunctionTerm(t);
            return;
        }

        final String name;
        {
            final String opName = t.op().name().toString();

            final String[] specialJmlKeywords = new String[] { "value" };

            if (Arrays.binarySearch(specialJmlKeywords, opName) >= 0
                    || Arrays.stream(JMLTranslator.JMLKeyWord.values()).map(JMLKeyWord::jmlName)
                            .anyMatch(opName::equals)) {
                name = "\\" + opName;
            } else {
                name = "\\dl_" + opName;
            }
        }

        startTerm(t.arity());
        layouter.print(name);
        if (t.arity() > 0) {
            layouter.print("(").beginC(0);
            for (int i = 0, n = t.arity(); i < n; i++) {
                markStartSub();
                printTerm(t.sub(i));
                markEndSub();

                if (i < n - 1) {
                    layouter.print(",").brk(1, 0);
                }
            }
            layouter.print(")").end();
        }
    }

    /**
     * Prints a term such that it can be parsed in JML.
     * 
     * @param term The {@link Term} to print.
     * @param services The {@link Services} object.
     * @return A JML term.
     */
    public static String printTerm(final Term term, final Services services) {
        final NotationInfo ni = new NotationInfo();

        final LogicPrinter p = new JMLLogicPrinter(new ProgramPrinter(), ni, services,
                new TermLabelVisibilityManager());

        if (services != null) {
            ni.refresh(services, true, false);
        }

        Map<Object, Notation> tbl = ni.getNotationTable();

        // While the parser is not fully capable, deactivate a few things.
        // @see: TacletMatchCompletionDialog
        final LocSetLDT setLDT = services.getTypeConverter().getLocSetLDT();
        tbl.remove(setLDT.getUnion());
        tbl.remove(setLDT.getIntersect());
        tbl.remove(setLDT.getSetMinus());
        tbl.remove(setLDT.getElementOf());
        tbl.remove(setLDT.getSubset());
        tbl.remove(setLDT.getEmpty());
        tbl.remove(IObserverFunction.class);
        tbl.remove(IProgramMethod.class);

        final int PRIORITY_EQUIVALENCE = 20;
        final int PRIORITY_IMP = 30;
        final int PRIORITY_OR = 40;
        final int PRIORITY_AND = 50;
        final int PRIORITY_MODALITY = 60;
        final int PRIORITY_EQUAL = 70;
        final int PRIORITY_COMPARISON = 80;
        final int PRIORITY_NEGATION = 100; // 60 in NotationInfo, but we need to put parentheses e.g. around negated equations

        // Add JML ops
        tbl.put(Junctor.AND,
                new Notation.Infix("&&", PRIORITY_AND, PRIORITY_AND, PRIORITY_MODALITY));
        tbl.put(Junctor.OR, new Notation.Infix("||", PRIORITY_OR, PRIORITY_OR, PRIORITY_AND));
        tbl.put(Junctor.IMP, new Notation.Infix("==>", PRIORITY_IMP, PRIORITY_OR, PRIORITY_IMP));
        tbl.put(Equality.EQV, new Notation.Infix("<==>", PRIORITY_EQUIVALENCE, PRIORITY_EQUIVALENCE,
                PRIORITY_IMP));
        tbl.put(Equality.class,
                new Notation.Infix("==", PRIORITY_EQUAL, PRIORITY_COMPARISON, PRIORITY_COMPARISON));
        tbl.put(Junctor.NOT, new Notation.Prefix("!", PRIORITY_NEGATION, PRIORITY_NEGATION));

        try {
            p.printTerm(term);
        } catch (IOException ioe) {
            return term.toString();
        }

        return p.result().toString();
    }
}