package de.tud.cs.se.ds.psec.compiler;

import org.objectweb.asm.Label;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

import de.tud.cs.se.ds.psec.compiler.taclet_translation.TacletTranslationFactory;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.operator.GreaterThan;
import de.uka.ilkd.key.java.statement.EmptyStatement;
import de.uka.ilkd.key.java.statement.Guard;
import de.uka.ilkd.key.java.statement.IGuard;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopInvariant;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Compiles the body of a method by Symbolic Execution.
 *
 * @author Dominic Scheurer
 */
public class MethodBodyCompiler implements Opcodes {
    private MethodVisitor mv;
    private String currentStatement;
    private ProgVarHelper pvHelper;
    private TacletTranslationFactory translationFactory;

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

        compile(startNode);
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
     * @param branchStatement
     */
    private void compile(IExecutionBranchStatement branchStatement) {

        // Currently considering ifSplit, ifElseSplit.
        // We assume that the guard is a boolean location variable that can be
        // loaded on to of the stack to decide about the split.
        // NOTE: We don't incorporate joining at the moment, so there will be
        // duplicate parts of code after the compilation of a split.

        Node branchNode = compileSequentialBlock(
                branchStatement.getProofNode());
        
        System.out.println(branchNode.serialNr() + ": "
                + branchNode.getAppliedRuleApp().rule().name());

        System.err.println(
                "[WARNING] Uncovered branching statement type: "
                        + branchStatement.getElementType()
                        + ", statement: " + currentStatement);
        // TODO
    }

    /**
     * TODO
     *
     * @param loopInvNode
     */
    private void compile(IExecutionLoopInvariant loopInvNode) {
        IGuard guard = loopInvNode.getLoopStatement().getGuard();

        // Jump-back label
        Label l0 = new Label();
        mv.visitLabel(l0);

        // Loop guard
        Label l1 = new Label();

        if (guard instanceof Guard && ((Guard) guard)
                .getExpression() instanceof GreaterThan) {
            GreaterThan gt = (GreaterThan) ((Guard) guard)
                    .getExpression();

            Expression first = gt.getArguments().get(0);
            Expression second = gt.getArguments().get(1);

            if (first instanceof LocationVariable
                    && second instanceof IntLiteral) {
                mv.visitVarInsn(ILOAD, pvHelper.progVarNr(
                        (LocationVariable) first));

                int cmpTo = Integer
                        .parseInt(((IntLiteral) second).getValue());
                if (cmpTo != 0) {
                    intConstInstruction((IntLiteral) second);
                    mv.visitInsn(IF_ICMPLE);
                } else {
                    mv.visitInsn(IFLE);
                }
            } else {
                System.err.println(
                        "[WARNING] Uncovered loop guard expression: "
                                + guard
                                + ", only considering pairs of loc vars "
                                + "and int literals currently");
            }
        } else {
            System.err.println(
                    "[WARNING] Uncovered loop guard expression: "
                            + guard);
        }

        // Loop body
        compile(loopInvNode.getChildren()[0]);

        // End while
        mv.visitJumpInsn(GOTO, l0);
        mv.visitLabel(l1);

        // Code after the loop
        compile(loopInvNode.getChildren()[1]);
    }

    /**
     * TODO
     *
     * @param startNode
     */
    private void compile(IExecutionNode<?> startNode) {
        //@formatter:off
        //TODO Note to self: Use a different approach. Start with an IExecutionNode, but
        //     compile using the intermediate steps by translating the taclet apps for
        //     nodes with node.getNodeInfo().getActiveStatement() until the next IExecutionNode.
        //     Use SymbolicExecutionUtil#isSymbolicExecutionTreeNode(...) for checking whether
        //     we arrived at the next node already.
        //     Have to take care of program variables introduced by KeY; however, we can treat
        //     local variables as equivalent if their names are equal, since KeY does the renaming
        //     for disambiguation.
        //@formatter:on

        IExecutionNode<?> currentNode = startNode;
        while (currentNode != null && currentNode.getChildren().length > 0) {
            
            // XXX Special case: "Use Operation Contract" has only one
            // *abstract* SET child, but two in the KeY proof tree. Have
            // to consider this. Maybe somehow deactivate all non-SE branches...
            
            if (currentNode.getChildren().length > 1) {

                // Note: Stack Map Frames are not generated manually here;
                // we're trying to leave it to the ASM framework to generate
                // them automatically. Computing the right values of these
                // frames is very difficult...
                // http://chrononsystems.com/blog/java-7-design-flaw-leads-to-huge-backward-step-for-the-jvm
                // http://asm.ow2.org/doc/developer-guide.html#classwriter

                currentStatement = currentNode.toString();

                // TODO: Treat all branches
                if (currentNode instanceof IExecutionLoopInvariant) {
                    compile((IExecutionLoopInvariant) currentNode);
                } else if (currentNode instanceof IExecutionBranchStatement) {
                    compile((IExecutionBranchStatement) currentNode);
                } else {
                    // TODO Is there more to support?
                    System.err.println(
                            "[ERROR] Unexpected branching statement type: "
                                    + currentNode.getElementType()
                                    + ", statement: " + currentStatement);
                }

                currentNode = null;

            } else {

                currentStatement = currentNode.toString();
                compileSequentialBlock(currentNode.getProofNode());

                // Stop after return; in KeY, there might be one more SE
                // statement where the result variable is assigned the return
                // value.
                // XXX: Is that really sound???
                if (currentNode instanceof IExecutionMethodReturn) {
                    currentNode = null;
                } else {
                    currentNode = currentNode.getChildren()[0];
                }

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
    private Node compileSequentialBlock(Node currentProofNode) {
        if (getOpenChildrenCount(currentProofNode) > 1) {
            return currentProofNode;
        }

        do {
            RuleApp app = currentProofNode.getAppliedRuleApp();
            if (hasNonEmptyActiveStatement(currentProofNode)) {
                compile(app);
            }

            if (currentProofNode.childrenCount() > 0) {
                currentProofNode = currentProofNode.child(0);
            } else {
                currentProofNode = null;
            }
        } while (currentProofNode != null
                && currentProofNode.childrenCount() < 2
                && !SymbolicExecutionUtil.isSymbolicExecutionTreeNode(
                        currentProofNode,
                        currentProofNode.getAppliedRuleApp()));

        return currentProofNode;
    }

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

    /**
     * TODO
     *
     * @param ruleApp
     */
    private void compile(RuleApp ruleApp) {
        if (ruleApp instanceof TacletApp) {
            TacletApp app = (TacletApp) ruleApp;
            translationFactory
                    .getTranslationForTacletApp(app).compile(app);
        } else {
            // TODO Are there other cases to support?
            System.err.println(
                    "[WARNING] Did not translate the following app: "
                            + ruleApp.rule().name() + ", statement: "
                            + currentStatement);
        }
    }

    /**
     * TODO
     *
     * @param lit
     */
    private void intConstInstruction(IntLiteral lit) {
        int theInt = Integer.parseInt(lit.toString());

        if (theInt < -1 || theInt > 5) {
            if (theInt >= Byte.MIN_VALUE && theInt <= Byte.MAX_VALUE) {
                mv.visitIntInsn(BIPUSH, theInt);
            } else if (theInt >= Short.MIN_VALUE && theInt <= Short.MAX_VALUE) {
                mv.visitIntInsn(SIPUSH, theInt);
            } else {
                System.err.println(
                        "[WARNING] Constants in full Integer range not yet covered, given: "
                                + theInt);
            }
        } else if (theInt == -1) {
            mv.visitInsn(ICONST_M1);
        } else if (theInt == 0) {
            mv.visitInsn(ICONST_0);
        } else if (theInt == 1) {
            mv.visitInsn(ICONST_1);
        } else if (theInt == 2) {
            mv.visitInsn(ICONST_2);
        } else if (theInt == 3) {
            mv.visitInsn(ICONST_3);
        } else if (theInt == 4) {
            mv.visitInsn(ICONST_4);
        } else if (theInt == 5) {
            mv.visitInsn(ICONST_5);
        }
    }
}
