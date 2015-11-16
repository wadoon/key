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

import java.util.LinkedList;
import java.util.ListIterator;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.expression.ExpressionStatement;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.statement.Branch;
import de.uka.ilkd.key.java.statement.Break;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.Continue;
import de.uka.ilkd.key.java.statement.Do;
import de.uka.ilkd.key.java.statement.EnhancedFor;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.Guard;
import de.uka.ilkd.key.java.statement.IForUpdates;
import de.uka.ilkd.key.java.statement.ILoopInit;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.Return;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

/**
 * Walks through a java AST in depth-left-fist-order. This walker is used to
 * transform a loop (not only while loops) according to the rules of the dynamic
 * logic.
 */
public class WhileInvariantTransformation extends WhileLoopTransformation {

    private JavaInfo javaInfo = null;

    private ProgramVariable cont = null;
    private ProgramVariable exc = null;
    private ProgramVariable rtrn = null;
    private ProgramVariable brk = null;
    private ProgramVariable thrownExc = null;
    private ProgramVariable excParam = null;
    private ProgramVariable returnExpr = null;

    private boolean continueOccurred = false;
    private boolean returnOccurred = false;

    private LinkedList<BreakToBeReplaced> breakList = null;

    /**
     * creates the WhileLoopTransformation for the transformation mode
     * 
     * @param root
     *            the ProgramElement where to begin
     * @param outerLabel
     *            the ProgramElementName of the outer label
     * @param innerLabel
     *            the ProgramElementName of the inner label
     */
    public WhileInvariantTransformation(ProgramElement root,
            ProgramElementName outerLabel, ProgramElementName innerLabel,
            ProgramVariable cont, ProgramVariable exc,
            ProgramVariable excParam, ProgramVariable thrownException,
            ProgramVariable brk, ProgramVariable rtrn,
            ProgramVariable returnExpr,
            LinkedList<BreakToBeReplaced> breakList, Services services) {

        super(root, outerLabel, innerLabel, services);
        this.cont = cont;
        this.exc = exc;
        this.excParam = excParam;
        this.thrownExc = thrownException;
        this.rtrn = rtrn;
        this.brk = brk;
        this.returnExpr = returnExpr;
        this.breakList = breakList;
        this.javaInfo = this.services.getJavaInfo();
    }

    /**
     * creates the WhileLoopTransformation for the check mode
     * 
     * @param root
     *            the ProgramElement where to begin
     * @param inst
     *            the SVInstantiations if available
     */
    public WhileInvariantTransformation(ProgramElement root,
            SVInstantiations inst, Services services) {
        super(root, inst, services);
        this.breakList = new LinkedList<BreakToBeReplaced>();
    }

    /**
     * returns true iff the loop to be transformed contains a continue referring
     * to this loop
     */
    public boolean continueOccurred() {
        return continueOccurred;
    }

    /**
     * return true iff the loop to be transformed contains a return statement
     * leading to abrupt termination of the loop body
     */
    public boolean returnOccurred() {
        return returnOccurred;
    }

    /**
     * returns a list of breaks that lead to abrupt termination of the loop and
     * have to be replaced
     */
    public LinkedList<BreakToBeReplaced> breakList() {
        return breakList;
    }

    public void performActionOnReturn(Return x) {
        boolean matched = true;
        if (!methodStack.empty())
            methodStack.pop();
        else
            matched = false;

        if (!matched) {
            if (runMode == CHECK) {
                needInnerLabel = true;
            }
            else {
                ExtList changeList = stack.peek();
                if (!changeList.isEmpty() && changeList.getFirst() == CHANGED) {
                    changeList.removeFirst();
                }
                returnOccurred = true;
                Statement assignFlag =
                        KeYJavaASTFactory.assign(rtrn, BooleanLiteral.TRUE);
                final StatementBlock stmnts;
                if (returnExpr != null) {
                    // Keep the PositionInfo because it is required for symbolic
                    // execution tree extraction and this assignment is the only
                    // unique representation of the replaced return
                    Statement assignExpr =
                            KeYJavaASTFactory.assign(returnExpr,
                                    x.getExpression(), x.getPositionInfo());
                    stmnts =
                            KeYJavaASTFactory.block(assignFlag, assignExpr,
                                    breakInnerLabel);
                }
                else
                    // Keep the PositionInfo because it is required for symbolic
                    // execution tree extraction and there is no other unique
                    // representation of the replaced return
                    stmnts =
                            KeYJavaASTFactory.block(assignFlag,
                                    KeYJavaASTFactory.breakStatement(
                                            breakInnerLabel.getLabel(),
                                            x.getPositionInfo()));
                addChild(stmnts);
                changed();
            }
        }
        else
            doDefaultAction(x);
    }

    public void performActionOnContinue(Continue x) {
        if (replaceJumpStatement(x)
                || ((x.getLabel() != null) && (labelStack.search(x.getLabel()) == -1))) {
            continueOccurred = true;
            if (runMode == CHECK) {
                needInnerLabel = true;
            }
            else {
                Statement assign =
                        KeYJavaASTFactory.assign(cont, BooleanLiteral.TRUE);
                // Keep the PositionInfo because it is required for symbolic
                // execution tree extraction and there is no other unique
                // representation of the replaced continue
                addChild(KeYJavaASTFactory.block(assign, KeYJavaASTFactory
                        .breakStatement(breakInnerLabel.getLabel(),
                                x.getPositionInfo())));
                changed();
            }
        }
        else {
            doDefaultAction(x);
        }
    }

    public void performActionOnBreak(Break x) {
        boolean replaced = false;
        if (replaceJumpStatement(x)
                || ((x.getLabel() != null) && (labelStack.search(x.getLabel()) == -1))) {
            if (runMode == CHECK) {
                needInnerLabel = true;
                breakList.add(new BreakToBeReplaced(x));
            }
            else {
                ListIterator<BreakToBeReplaced> it = breakList.listIterator(0);
                while (it.hasNext()) {
                    BreakToBeReplaced b = it.next();
                    if (x == b.getBreak()) {
                        Statement assignFlag =
                                KeYJavaASTFactory.assign(brk,
                                        BooleanLiteral.TRUE);
                        // Keep the PositionInfo because it is required for
                        // symbolic execution tree extraction and this
                        // assignment is the only unique representation of the
                        // replaced break
                        Statement assign =
                                KeYJavaASTFactory.assign(
                                        b.getProgramVariable(),
                                        BooleanLiteral.TRUE,
                                        x.getPositionInfo());
                        replaced = true;
                        addChild(KeYJavaASTFactory.block(assignFlag, assign,
                                breakInnerLabel));
                        changed();
                        break;
                    }
                }
                if (!replaced)
                    doDefaultAction(x);
            }
        }
        else {
            doDefaultAction(x);
        }
    }

    @Override
    public void performActionOnWhile(While x) {
        ExtList changeList = stack.peek();
        if (replaceBreakWithNoLabel == 0) {
            // the most outer while loop
            // get guard
            if (changeList.getFirst() == CHANGED) {
                changeList.removeFirst();
            }
            @SuppressWarnings("unused")
            Expression guard =
                    ((Guard) changeList.removeFirst()).getExpression();
            Statement body =
                    (Statement) (changeList.isEmpty() ? null : changeList
                            .removeFirst());

            body = KeYJavaASTFactory.ifThen(x.getGuardExpression(), body);
            if (breakInnerLabel != null) {
                // an unlabeled continue needs to be handled with (replaced)
                body =
                        KeYJavaASTFactory.labeledStatement(
                                breakInnerLabel.getLabel(), body,
                                PositionInfo.UNDEFINED);
            }
            StatementBlock block = KeYJavaASTFactory.block(body);
            Statement newBody = block;
            if (breakOuterLabel != null) {
                // an unlabeled break occurs in the
                // while loop therefore we need a labeled statement
                newBody =
                        KeYJavaASTFactory.labeledStatement(
                                breakOuterLabel.getLabel(), block,
                                PositionInfo.UNDEFINED);

            }

            Statement[] catchStatements =
                    { KeYJavaASTFactory.assign(exc, BooleanLiteral.TRUE),
                            KeYJavaASTFactory.assign(thrownExc, excParam) };

            Catch ctch =
                    KeYJavaASTFactory.catchClause(KeYJavaASTFactory
                            .parameterDeclaration(javaInfo, javaInfo
                                    .getKeYJavaType("java.lang.Throwable"),
                                    excParam), catchStatements);

            Branch[] branch = { ctch };
            Statement res = KeYJavaASTFactory.tryBlock(newBody, branch);
            addChild(res);
            changed();
        }
        else {
            if (changeList.getFirst() == CHANGED) {
                changeList.removeFirst();
            }

            // if (!changeList.isEmpty()) {

            Expression guard =
                    ((Guard) changeList.removeFirst()).getExpression();
            Statement body =
                    (Statement) (changeList.isEmpty() ? null : changeList
                            .removeFirst());

            body = resetBrkVariableToDefVal(body);


            final While newLoop = KeYJavaASTFactory.whileLoop(guard, body, x.getPositionInfo());
            services.getSpecificationRepository().copyLoopInvariant(x, newLoop);
            StatementBlock block = 
                    insertBreakReinitializationAferLoopStatement(newLoop);

            addChild(block);
            changed();

            // } else {
            // doDefaultAction(x);
            // }
        }
    }

    /**
     * TODO: Document.
     *
     * @param body
     * @return
     */
    private Statement resetBrkVariableToDefVal(Statement body) {
        ImmutableList<Statement> bodyList;
        if (body instanceof StatementBlock) {
            bodyList = ((StatementBlock) body).getBody().toImmutableList();
        }
        else {
            bodyList = ImmutableSLList.<Statement>nil();
            bodyList = bodyList.prepend(body);
        }

        bodyList = reinitializeBreakVariables(bodyList);

        body =
                KeYJavaASTFactory.block(bodyList.toArray(Statement.class));
        return body;
    }

    private ImmutableList<Statement> reinitializeBreakVariables(
            ImmutableList<Statement> bodyList) {
        for (BreakToBeReplaced btbr : breakList) {
            bodyList =
                    bodyList.prepend(KeYJavaASTFactory.assign(
                            btbr.getProgramVariable(), BooleanLiteral.FALSE));
        }
        bodyList = bodyList.prepend(KeYJavaASTFactory.assign(brk, BooleanLiteral.FALSE));
        bodyList = bodyList.prepend(KeYJavaASTFactory.assign(rtrn, BooleanLiteral.FALSE));
        bodyList = bodyList.prepend(KeYJavaASTFactory.assign(exc, BooleanLiteral.FALSE));
        return bodyList;
    }

    @Override
    public void performActionOnDo(Do x) {
        ExtList changeList = stack.peek();
        if (replaceBreakWithNoLabel == 0) {
            // the most outer do loop
            if (changeList.getFirst() == CHANGED) {
                changeList.removeFirst();
            }
            Statement body =
                    (Statement) (changeList.isEmpty() ? null : changeList
                            .removeFirst());

            Expression guard =
                    ((Guard) changeList.removeFirst()).getExpression();
            Statement unwindedBody = null;
            if (innerLabelNeeded() && breakInnerLabel != null) {
                // an unlabeled continue needs to be handled with (replaced)
                unwindedBody =
                        KeYJavaASTFactory.labeledStatement(
                                breakInnerLabel.getLabel(), body,
                                PositionInfo.UNDEFINED);
            }
            else {
                unwindedBody = body;
            }
            Statement resultStatement = null;
            While newLoop =
                    KeYJavaASTFactory.whileLoop(guard, x.getBody(),
                            x.getPositionInfo());
            services.getSpecificationRepository().copyLoopInvariant(x, newLoop);
            StatementBlock block =
                    KeYJavaASTFactory.block(unwindedBody, newLoop);

            if (outerLabelNeeded() && breakOuterLabel != null) {
                // an unlabeled break occurs in the
                // body therefore we need a labeled statement
                resultStatement =
                        KeYJavaASTFactory.labeledStatement(
                                breakOuterLabel.getLabel(), block,
                                PositionInfo.UNDEFINED);
            }
            else {
                resultStatement = block;
            }
            addChild(resultStatement);
            changed();
        }
        else {
            if (changeList.getFirst() == CHANGED) {
                changeList.removeFirst();
            }

            Statement body = changeList.removeFirstOccurrence(Statement.class);

            body = resetBrkVariableToDefVal(body);

            Guard g = changeList.removeFirstOccurrence(Guard.class);
            Expression guard = g == null ? null : g.getExpression();
            LoopStatement newLoop =
                    KeYJavaASTFactory.doLoop(guard, body, x.getPositionInfo());            
            services.getSpecificationRepository().copyLoopInvariant(x, newLoop);

            StatementBlock block = insertBreakReinitializationAferLoopStatement(
                    newLoop);
            
            addChild(block);
            changed();
        }
    }

    private StatementBlock insertBreakReinitializationAferLoopStatement(
            LoopStatement newLoop) {
        StatementBlock block = 
                new StatementBlock(reinitializeBreakVariables(ImmutableSLList.<Statement>nil()).prepend(newLoop).toArray(Statement.class));
        return block;
    }

    /**
     * Transform the body of an enhanced for loop for usage with
     * invariant-theorems.
     * 
     * The following restriction is made for enhanced for loops: There is only
     * one label (no inner/outer pair) needed, so innerlabel and outerlabel must
     * be the same.
     * 
     * The loop body is transformed like for a while loop (break/continue/return
     * replaced, try+catch added).
     * 
     * If the top loop is an enhancedFor-loop transform it like a while loop.
     * 
     * Due to the fact that the condition in enhanced loops has no side effects,
     * things can be put easier here.
     * 
     * If the loop is not top most, act like the super class.
     */
    public void performActionOnEnhancedFor(EnhancedFor x) {
        ExtList changeList = stack.peek();
        if (replaceBreakWithNoLabel == 0) {
            if (changeList.getFirst() == CHANGED) {
                changeList.removeFirst();
            }

            if (breakInnerLabel != breakOuterLabel)
                Debug.log4jWarn(
                        "inner and outer label must be the same in WhileInvariantTransformation.performActionOnEnhancedFor",
                        null);

            Statement body = changeList.get(Statement.class);

            // label statement if there are returns / continue / breaks
            if (breakOuterLabel != null) {
                body =
                        KeYJavaASTFactory.labeledStatement(
                                breakOuterLabel.getLabel(), body,
                                PositionInfo.UNDEFINED);

            }

            Statement[] catchStatements =
                    { KeYJavaASTFactory.assign(exc, BooleanLiteral.TRUE),
                            KeYJavaASTFactory.assign(thrownExc, excParam) };

            Catch ctch =
                    KeYJavaASTFactory.catchClause(KeYJavaASTFactory
                            .parameterDeclaration(javaInfo, javaInfo
                                    .getKeYJavaType("java.lang.Throwable"),
                                    excParam), catchStatements);

            addChild(KeYJavaASTFactory.tryBlock(body, ctch));
            changed();
        }
        else {
            if (changeList.getFirst() == CHANGED) {
                changeList.removeFirst();
            }

            Statement body = changeList.get(Statement.class);

            body = resetBrkVariableToDefVal(body);

            changeList.addFirst(body);

            EnhancedFor newLoop = KeYJavaASTFactory.enhancedForLoop(changeList);
            services.getSpecificationRepository().copyLoopInvariant(x, newLoop);
            StatementBlock block = insertBreakReinitializationAferLoopStatement(
                    newLoop);

            addChild(block);
            changed();
        }
    }

    @Override
    public void performActionOnFor(For x) {
        ExtList changeList = stack.peek();
        if (replaceBreakWithNoLabel == 0) {
            // most outer for loop
            if (changeList.getFirst() == CHANGED)
                changeList.removeFirst();

            ILoopInit inits = null;

            IForUpdates updates = null;

            // the unchanged updates need to be extracted to initialize the
            // remaining 'for' statement
            IForUpdates unchangedUpdates = x.getIForUpdates();

            Guard guard;
            Statement body = null;

            if (changeList.get(0) instanceof ILoopInit) {
                inits = (ILoopInit) changeList.removeFirst();
            }

            if (x.getGuard() != null) {
                guard = (Guard) changeList.removeFirst();
                if (guard.getExpression() == null) {
                    guard = KeYJavaASTFactory.trueGuard();
                }
            }
            else {
                guard = KeYJavaASTFactory.trueGuard();
            }

            if (changeList.get(0) instanceof IForUpdates) {
                updates = (IForUpdates) changeList.removeFirst();
            }
            body = (Statement) changeList.removeFirst();

            For remainder =
                    KeYJavaASTFactory.forLoop(x.getGuard(), unchangedUpdates,
                            x.getBody());

            if (innerLabelNeeded() && breakInnerLabel != null) {
                body =
                        KeYJavaASTFactory.labeledStatement(
                                breakInnerLabel.getLabel(), body,
                                PositionInfo.UNDEFINED);
            }

            final int updateSize = updates == null ? 0 : updates.size();
            Statement innerBlockStatements[] = new Statement[updateSize + 2];
            innerBlockStatements[0] = body;

            if (updates != null) {
                for (int copyStatements = 0; copyStatements < updateSize; copyStatements++) {
                    innerBlockStatements[copyStatements + 1] =
                            (ExpressionStatement) updates
                                    .getExpressionAt(copyStatements);
                }
            }
            innerBlockStatements[updateSize + 1] = remainder;

            final int initSize = inits == null ? 0 : inits.size();

            final Statement outerBlockStatements[] =
                    new Statement[initSize + 1];

            if (inits != null) {
                for (int copyStatements = 0; copyStatements < initSize; copyStatements++) {
                    outerBlockStatements[copyStatements] =
                            inits.getInits().get(copyStatements);
                }
            }

            outerBlockStatements[initSize] =
                    KeYJavaASTFactory.ifThen(guard.getExpression(),
                            innerBlockStatements);

            if (outerLabelNeeded() && breakOuterLabel != null) {
                addChild(KeYJavaASTFactory.labeledStatement(
                        breakOuterLabel.getLabel(), outerBlockStatements,
                        PositionInfo.UNDEFINED));
            }
            else {
                addChild(KeYJavaASTFactory.block(outerBlockStatements));
            }
            changed();
        }
        else {

            if (changeList.getFirst() == CHANGED) {
                changeList.removeFirst();
            }

            Statement body = changeList.get(Statement.class);

            body = resetBrkVariableToDefVal(body);

            changeList.addFirst(body);

            For newLoop = KeYJavaASTFactory.forLoop(changeList);
            services.getSpecificationRepository().copyLoopInvariant(x, newLoop);
            StatementBlock block = insertBreakReinitializationAferLoopStatement(
                    newLoop);
            addChild(block);
            changed();
        }
    }

}
