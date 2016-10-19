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

/**
 * TODO
 * 
 * @author Dominic Scheurer
 * @see ForToWhile
 */

public class LoopComplexToSimple extends ProgramTransformer {

    /**
     * TODO
     * 
     * @param schemaVariable
     */
    public LoopComplexToSimple(While loop) {
        super("#loop-complex-to-simple", loop);
    }

    /**
     * TODO
     */
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

        return KeYJavaASTFactory.block(exprEvaluation,
                KeYJavaASTFactory.whileLoop(newBoolVar, newBlock));
    }

    /**
     * TODO
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