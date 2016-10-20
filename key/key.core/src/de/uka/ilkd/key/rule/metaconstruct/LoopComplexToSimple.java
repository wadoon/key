// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.Continue;
import de.uka.ilkd.key.java.statement.EnhancedFor;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.java.visitor.ProgramReplaceVisitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopInvariant;

/**
 * Converts a loop with a non-simple guard expression into one with a simple
 * guard expression, that is only having a boolean program variables as a guard
 * which is "manually" updated before each loop repetition.
 * 
 * <h2>Example</h2>
 * 
 * <pre>
 * while (++x < 42) {
 *     if (i == 2)
 *         continue;
 *     if (i == 3)
 *         break;
 * 
 *     int j = 1;
 *     while (j++ < 3) {
 *         continue;
 *     }
 * }
 * </pre>
 * 
 * is translated to
 * 
 * <pre>
 * boolean b = (++x < 42);
 * while (b) {
 *     if (i == 2) {
 *         b = (++x < 42);
 *         continue; // Relevant continue
 *     }
 *     if (i == 3)
 *         break;
 * 
 *     int j = 1;
 *     while (j++ < 3) {
 *         continue; // Continue in other loop scope
 *     }
 * 
 *     b = (++x < 42); // Update before regular loop repetition
 * }
 * </pre>
 * 
 * @author Dominic Scheurer
 * @see ForToWhile
 */

public class LoopComplexToSimple extends ProgramTransformer {

    /**
     * @param loop
     *            The {@link While} loop to be transformed.
     */
    public LoopComplexToSimple(While loop) {
        super("#loop-complex-to-simple", loop);
    }

    @Override
    public ProgramElement transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        assert pe instanceof While;
        TermBuilder tb = services.getTermBuilder();

        StatementBlock bodyBlock = (StatementBlock) ((While) pe).getBody();
        Expression complexGuard = ((While) pe).getGuardExpression();

        KeYJavaType boolType = services.getJavaInfo().getKeYJavaType("boolean");
        LocationVariable newBoolVar = new LocationVariable(
                new ProgramElementName(tb.newName(boolType.getSort())),
                boolType);

        Statement exprEvaluation = KeYJavaASTFactory.assign(newBoolVar,
                complexGuard);

        GuardEvaluationBeforeContinueVisitor transf = //
                new GuardEvaluationBeforeContinueVisitor( //
                        exprEvaluation, //
                        bodyBlock, //
                        services);

        transf.start();

        StatementBlock newBlock = KeYJavaASTFactory
                .block((StatementBlock) transf.result(), exprEvaluation);

        Statement newLoop = KeYJavaASTFactory.whileLoop(newBoolVar, newBlock);

        // Re-attach loop invariant, if present
        LoopInvariant li = services.getSpecificationRepository()
                .getLoopInvariant((While) pe);

        if (li != null) {
            li = li.setLoop((While) newLoop);
            services.getSpecificationRepository().addLoopInvariant(li);
        }

        return KeYJavaASTFactory.block(exprEvaluation, newLoop);
    }

    /**
     * A {@link ProgramReplaceVisitor} adding a given {@link Statement} before
     * any continue in the current "loop scope", that is not in the scope of any
     * inner loop.
     *
     * @author Dominic Scheurer
     */
    class GuardEvaluationBeforeContinueVisitor extends ProgramReplaceVisitor {
        private Statement stmtToAddBeforeContinue;
        private boolean insideInnerLoop = false;
        private int firstInnerLoopDepth = -1;

        public GuardEvaluationBeforeContinueVisitor(
                Statement stmtToAddBeforeContinue, ProgramElement root,
                Services services) {
            super(root, services, null);
            this.stmtToAddBeforeContinue = stmtToAddBeforeContinue;
        }

        @Override
        protected void walk(ProgramElement node) {
            if (insideInnerLoop && depth() <= firstInnerLoopDepth) {
                insideInnerLoop = false;
            }

            if (!insideInnerLoop
                    && ((node instanceof While) || (node instanceof For)
                            || (node instanceof EnhancedFor))) {
                insideInnerLoop = true;
                firstInnerLoopDepth = depth();
            }

            super.walk(node);
        }

        @Override
        public void performActionOnContinue(Continue x) {
            if (insideInnerLoop) {
                super.performActionOnContinue(x);
            } else {
                changed();
                defaultAction(x, //
                        (extList -> //
                        new StatementBlock(stmtToAddBeforeContinue, //
                                new Continue(extList))) //
                ).doAction(x);
            }
        }
    }
}