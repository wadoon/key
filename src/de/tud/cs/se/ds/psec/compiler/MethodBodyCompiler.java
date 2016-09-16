package de.tud.cs.se.ds.psec.compiler;

import java.util.Optional;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.compiler.ast.TacletTranslationFactory;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.statement.EmptyStatement;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Compiles the body of a method by Symbolic Execution.
 *
 * @author Dominic Scheurer
 */
public class MethodBodyCompiler implements Opcodes {
    private static final Logger logger = LogManager.getFormatterLogger();

    private MethodVisitor mv;
    private String currentStatement;
    private ProgVarHelper pvHelper;
    private TacletTranslationFactory translationFactory;
    private TacletASTNode astRoot;

    /**
     * TODO
     * 
     * @param mv
     * @param isStatic
     *            TODO
     */
    public MethodBodyCompiler(MethodVisitor mv,
            Iterable<ParameterDeclaration> methodParameters, boolean isStatic) {
        this.mv = mv;
        this.pvHelper = new ProgVarHelper(isStatic);
        this.translationFactory = new TacletTranslationFactory(mv, pvHelper);

        methodParameters.forEach(p -> pvHelper.progVarNr(
                p.getVariables().get(0).getProgramVariable()));
    }

    /**
     * Compiles the content of the symbolic execution tree given by
     * {@link SymbolicExecutionTreeBuilder} using the {@link MethodVisitor}
     * supplied to the constructor {@link #MethodBodyCompiler(MethodVisitor)}.
     *
     * @param builder
     *            {@link SymbolicExecutionTreeBuilder} resulting from execution
     *            of the method's body.
     */
    public void compile(SymbolicExecutionTreeBuilder builder) {
        // Forward until after call of this method
        IExecutionNode<?> startNode = ffUntilAfterFirstMethodCall(builder);
        findASTRoot(startNode);
        
        compile(startNode, astRoot);
    }

    /**
     * "Fast-forwards" the tree until the first statement after the first method
     * call in the tree.
     *
     * @param builder
     * @return
     */
    private IExecutionNode<?> ffUntilAfterFirstMethodCall(
            SymbolicExecutionTreeBuilder builder) {
        IExecutionNode<?> startNode = builder.getStartNode();
        while (!(startNode instanceof IExecutionMethodCall)) {
            startNode = startNode.getChildren()[0];
        }
        startNode = startNode.getChildren()[0];
        return startNode;
    }

    /**
     * TODO
     *
     * @param rootOfSET
     */
    private void findASTRoot(IExecutionNode<?> rootOfSET) {
        // TODO Unchecked conversion to TacletApp... Problematic if there is a
        // RuleApp like LoopInvariant first. In this case, also have to support
        // more general translations for that case...
        Node currentProofNode = rootOfSET.getProofNode();
        while (!translationFactory.getTranslationForTacletApp(
                (TacletApp) currentProofNode.getAppliedRuleApp()).isPresent()) {
            // TODO Assume that there is a child, and exactly one. Insert more
            // checks.
            currentProofNode = currentProofNode.child(0);
        }

        astRoot = translationFactory.getTranslationForTacletApp(
                (TacletApp) currentProofNode.getAppliedRuleApp()).get();
    }

    /**
     * TODO
     *
     * @param startNode
     */
    private void compile(IExecutionNode<?> startNode, TacletASTNode astStartNode) {
        IExecutionNode<?> currentNode = startNode;

        while (currentNode != null && currentNode.getChildren().length > 0) {

            // XXX Special case: "Use Operation Contract" has only one
            // *abstract* SET child, but two in the KeY proof tree. Have
            // to consider this. Maybe somehow deactivate all non-SE branches...
            
            TacletASTNode currentASTNode = 
                    compileSequentialBlock(currentNode.getProofNode(), astStartNode);

            currentStatement = currentNode.toString();

            if (currentNode.getChildren().length > 1) {

                // Note: Stack Map Frames are not generated manually here;
                // we're trying to leave it to the ASM framework to generate
                // them automatically. Computing the right values of these
                // frames is very difficult...
                // http://chrononsystems.com/blog/java-7-design-flaw-leads-to-huge-backward-step-for-the-jvm
                // http://asm.ow2.org/doc/developer-guide.html#classwriter
                
                for (IExecutionNode<?> child : currentNode.getChildren()) {
                    compile(child, currentASTNode);
                }

                currentNode = null;

            }
        }
    }

    /**
     * Compiles all SE statements until the next node that's part of the
     * abstract SET, where the last compiled node must have exactly one child.
     * That is, compilation stops at a splitting rule and at the end of the
     * proof tree.
     *
     * @param currentProofNode
     *            The starting point for compilation of the block.
     * @return The successor of the node that was processed at last.
     */
    private TacletASTNode compileSequentialBlock(Node currentProofNode, TacletASTNode astStartNode) {
        if (getOpenChildrenCount(currentProofNode) > 1) {
            return astStartNode;
        }
        
        TacletASTNode astCurrentNode = astStartNode;

        do {
            RuleApp app = currentProofNode.getAppliedRuleApp();
            Optional<TacletASTNode> newNode = Optional.empty();
            if (hasNonEmptyActiveStatement(currentProofNode)) {
                newNode = toASTNode(app);
            }

            if (currentProofNode.childrenCount() > 0) {
                currentProofNode = currentProofNode.child(0);
                
                if (newNode.isPresent()) {
                    astCurrentNode.addChild(newNode.get());
                    astCurrentNode = newNode.get();
                }
            } else {
                currentProofNode = null;
            }
        } while (currentProofNode != null
                && currentProofNode.childrenCount() < 2
                && !SymbolicExecutionUtil.isSymbolicExecutionTreeNode(
                        currentProofNode,
                        currentProofNode.getAppliedRuleApp()));

        return astCurrentNode;
    }

    /**
     * TODO
     *
     * @param ruleApp
     */
    private Optional<TacletASTNode> toASTNode(RuleApp ruleApp) {
        if (ruleApp instanceof TacletApp) {
            TacletApp app = (TacletApp) ruleApp;
            return translationFactory
                    .getTranslationForTacletApp(app);
        } else {
            // TODO Are there other cases to support?
            logger.error(
                    "Did not translate the following app: %s, statement: %s",
                    ruleApp.rule().name(), currentStatement);
            return Optional.empty();
        }
    }

    //@formatter:off
//    /**
//     * TODO
//     *
//     * @param branchStatement
//     */
//    private void compile(IExecutionBranchStatement branchStatement) {
//        // Currently considering ifSplit, ifElseSplit.
//        // We assume that the guard is a boolean location variable that can be
//        // loaded on to of the stack to decide about the split.
//        // NOTE: We don't incorporate merging at the moment, so there will be
//        // duplicate parts of code after the compilation of a split.
//        // Furthermore, all if-split rules have two descendants, even if there
//        // is no explicit else part.
//
//        logger.trace("Compiling %s", branchStatement);
//
//        Node branchNode = compileSequentialBlock(
//                branchStatement.getProofNode());
//
//        TacletApp app = (TacletApp) branchNode.getAppliedRuleApp();
//
//        String ruleName = branchNode.getAppliedRuleApp().rule().name()
//                .toString();
//
//        if (!ruleName.equals("ifSplit") && !ruleName.equals("ifElseSplit")) {
//            logger.error(
//                    "Uncovered branching statement type: %s, statement: %s",
//                    branchStatement.getElementType(), currentStatement);
//        }
//
//        LocationVariable simpleBranchCondition = (LocationVariable) TacletASTNode
//                .getTacletAppInstValue("#se");
//
//        mv.visitVarInsn(ILOAD, pvHelper.progVarNr(simpleBranchCondition));
//
//        Label l1 = new Label();
//        mv.visitJumpInsn(IFEQ, l1);
//
//        // then-part. Don't have to GOTO the block after the if since state
//        // merging is not yet incorporated.
//        // XXX Make sure that the code doesn't reach the ELSE part if no
//        // explicit return statement is there (void methods)
//
//        compile(branchStatement.getChildren()[0]);
//
//        // else-part.
//        mv.visitLabel(l1);
//        compile(branchStatement.getChildren()[1]);
//    }
//
//    /**
//     * TODO
//     *
//     * @param loopInvNode
//     */
//    private void compile(IExecutionLoopInvariant loopInvNode) {
//        logger.trace("Compiling %s", loopInvNode);
//
//        // XXX Not yet working!!!
//
//        IGuard guard = loopInvNode.getLoopStatement().getGuard();
//
//        // Jump-back label
//        Label l0 = new Label();
//        mv.visitLabel(l0);
//
//        // Loop guard
//        Label l1 = new Label();
//
//        if (guard instanceof Guard && ((Guard) guard)
//                .getExpression() instanceof GreaterThan) {
//            GreaterThan gt = (GreaterThan) ((Guard) guard)
//                    .getExpression();
//
//            Expression first = gt.getArguments().get(0);
//            Expression second = gt.getArguments().get(1);
//
//            if (first instanceof LocationVariable
//                    && second instanceof IntLiteral) {
//                mv.visitVarInsn(ILOAD, pvHelper.progVarNr(
//                        (LocationVariable) first));
//
//                int cmpTo = Integer
//                        .parseInt(((IntLiteral) second).getValue());
//                if (cmpTo != 0) {
//                    intConstInstruction((IntLiteral) second);
//                    mv.visitInsn(IF_ICMPLE);
//                } else {
//                    mv.visitInsn(IFLE);
//                }
//            } else {
//                logger.error(
//                        "Uncovered loop guard expression: %s, only "
//                                + "considering pairs of loc vars and int "
//                                + "literals currently",
//                        guard);
//            }
//        } else {
//            logger.error(
//                    "Uncovered loop guard expression: %s",
//                    guard);
//        }
//
//        // Loop body
//        compile(loopInvNode.getChildren()[0]);
//
//        // End while
//        mv.visitJumpInsn(GOTO, l0);
//        mv.visitLabel(l1);
//
//        // Code after the loop
//        compile(loopInvNode.getChildren()[1]);
//    }
    //@formatter:on

    /**
     * Computes the number of open child branches of the given {@link Node}.
     *
     * @param node
     *            The {@link Node} whose open child branches to count.
     * @return The number of open child branches of the given {@link Node}.
     */
    private int getOpenChildrenCount(Node node) {
        int result = 0;
        for (int i = 0; i < node.childrenCount(); i++) {
            if (!node.child(i).isClosed()) {
                result++;
            }
        }

        return result;
    }

    /**
     * TODO
     *
     * @param node
     * @return
     */
    private static boolean hasNonEmptyActiveStatement(Node node) {
        SourceElement src = node.getNodeInfo()
                .getActiveStatement();

        return src != null && !src.getClass().equals(EmptyStatement.class)
                && !(src instanceof StatementBlock
                        && ((StatementBlock) src).isEmpty());
    }
}
