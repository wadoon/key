package de.tud.cs.se.ds.psec.compiler;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;

import org.objectweb.asm.Label;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.operator.GreaterThan;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.EmptyStatement;
import de.uka.ilkd.key.java.statement.Guard;
import de.uka.ilkd.key.java.statement.IGuard;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopInvariant;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * Compiles the body of a method by Symbolic Execution.
 *
 * @author Dominic Scheurer
 */
public class MethodBodyCompiler implements Opcodes {
    private MethodVisitor mv;
    private HashMap<IProgramVariable, Integer> progVarOffsetMap = new HashMap<>();
    private String currentStatement;

    /**
     * TODO
     * 
     * @param mv
     */
    public MethodBodyCompiler(MethodVisitor mv,
            Iterable<ParameterDeclaration> methodParameters) {
        this.mv = mv;
        methodParameters.forEach(p -> getNrForProgramVar(
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
     * @param progVar
     * @return
     */
    private int getNrForProgramVar(IProgramVariable progVar) {
        //XXX: Static methods don't have the "this" field as first variable!
        
        if (progVarOffsetMap.containsKey(progVar)) {
            return progVarOffsetMap.get(progVar);
        } else {
            // Offset 0 for "this" pointer, following ones for method
            // parameters, then for local variables.
            // XXX: Does this also work for variables with the same name
            // declared in different scopes?
            int offset = progVarOffsetMap.size() + 1;
            progVarOffsetMap.put(progVar, offset);
            return offset;
        }
    }

    /**
     * TODO
     *
     * @param startNode
     */
    private void compile(IExecutionNode<?> startNode) {
        //TODO Note to self: Use a different approach. Start with an IExecutionNode, but
        //     compile using the intermediate steps by translating the taclet apps for
        //     nodes with node.getNodeInfo().getActiveStatement() until the next IExecutionNode.
        //     Use SymbolicExecutionUtil#isSymbolicExecutionTreeNode(...) for checking whether
        //     we arrived at the next node already.
        //     Have to take care of program variables introduced by KeY; however, we can treat
        //     local variables as equivalent if their names are equal, since KeY does the renaming
        //     for disambiguation.
        
        Deque<IExecutionNode<?>> executionStack = new ArrayDeque<IExecutionNode<?>>();

        IExecutionNode<?> currentNode = startNode;
        while (currentNode != null && currentNode.getChildren().length > 0) {
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
                    IExecutionLoopInvariant loopInvNode = ((IExecutionLoopInvariant) currentNode);
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
                            mv.visitVarInsn(ILOAD, getNrForProgramVar((LocationVariable) first));
                            
                            int cmpTo = Integer.parseInt(((IntLiteral) second).getValue());
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
                    
                    // TODO
                } else if (currentNode instanceof IExecutionBranchStatement) {
                    // TODO
                    System.err.println(
                            "[WARNING] Uncovered branching statement type: "
                                    + currentNode.getElementType()
                                    + ", statement: " + currentStatement);
                } else {
                    // ...
                    // TODO Is there more to support?
                    System.err.println(
                            "[WARNING] Uncovered branching statement type: "
                                    + currentNode.getElementType()
                                    + ", statement: " + currentStatement);
                }

                currentNode = null;
            } else {
                // Store for later
                executionStack.push(currentNode);
                currentNode = currentNode.getChildren()[0];
            }
        }

        while ((currentNode = executionStack.pollFirst()) != null) {
            currentStatement = currentNode.toString();

            // Compile the node
            SourceElement src = currentNode.getProofNode().getNodeInfo()
                    .getActiveStatement();
            if (src == null || src.getClass().equals(EmptyStatement.class) ||
                    (src instanceof StatementBlock
                            && ((StatementBlock) src).isEmpty())) {
                continue;
            }

            compile(getRuleAppForExecNode(currentNode));
        }
    }

    /**
     * TODO
     *
     * @param app
     */
    private void compile(RuleApp app) {
        if (app instanceof TacletApp) {
            TacletApp tApp = (TacletApp) app;

            if (tApp.taclet().name()
                    .equals(new Name("variableDeclarationAssign"))) {
                TypeRef typeRef = (TypeRef) getTacletAppInstValue(tApp, "#t");

                if (!typeRef.toString().equals("int")) {
                    // TODO: Other types
                    System.err.println(
                            "[WARING] Only integer types considered so far, given: "
                                    + typeRef.toString() + ", statement: "
                                    + currentStatement);
                }

                LocationVariable locVar = (LocationVariable) getTacletAppInstValue(
                        tApp, "#v0");

                if (getTacletAppInstValue(tApp,
                        "#vi") instanceof LocationVariable) {
                    // Assigning the value of a location variable
                    // TODO
                } else if (getTacletAppInstValue(tApp,
                        "#vi") instanceof IntLiteral) {
                    // Assigning the value of a constant
                    intConstInstruction(
                            (IntLiteral) getTacletAppInstValue(tApp, "#vi"));
                } else {
                    // TODO
                }

                mv.visitVarInsn(ISTORE, getNrForProgramVar(locVar));
            } else {
                // TODO Support more taclets
                System.err.println(
                        "[WARNING] Did not translate the following taclet app: "
                                + app.rule().name() + ", statement: "
                                + currentStatement);
            }
        } else {
            // TODO What other cases to support?
            System.err.println(
                    "[WARNING] Did not translate the following taclet app: "
                            + app.rule().name() + ", statement: "
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

    /**
     * TODO
     *
     * @param node
     * @return
     */
    private static RuleApp getRuleAppForExecNode(IExecutionNode<?> node) {
        return node.getProofNode().getAppliedRuleApp();
    }

    /**
     * TODO
     *
     * @param app
     * @param sv
     * @return
     */
    private static Object getTacletAppInstValue(TacletApp app, String sv) {
        return app.instantiations()
                .lookupValue(new de.uka.ilkd.key.logic.Name(sv));
    }
}
