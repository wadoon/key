package de.tud.cs.se.ds.psec.compiler;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;

import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.EmptyStatement;
import de.uka.ilkd.key.java.statement.IGuard;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopInvariant;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * Compiles the body of a method by Symbolic Execution.
 *
 * @author Dominic Scheurer
 */
public class MethodBodyCompiler implements Opcodes {
    private MethodVisitor mv;
    private HashMap<IProgramVariable, Integer> progVarOffsetMap = new HashMap<>();

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
        compile(builder.getStartNode());
    }

    /**
     * TODO
     *
     * @param progVar
     * @return
     */
    private int getNrForProgramVar(IProgramVariable progVar) {
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
        Deque<IExecutionNode<?>> executionStack = new ArrayDeque<IExecutionNode<?>>();

        IExecutionNode<?> currentNode = startNode;
        while (currentNode != null && currentNode.getChildren().length > 0) {
            if (currentNode.getChildren().length > 1) {
                // TODO: Treat all branches
                if (currentNode instanceof IExecutionLoopInvariant) {
                    IExecutionLoopInvariant loopInvNode = ((IExecutionLoopInvariant) currentNode);
                    IGuard guard = loopInvNode.getLoopStatement().getGuard();

                    Node preservesInvBranch = loopInvNode.getChildren()[0]
                            .getProofNode();
                    Node useCaseBranch = loopInvNode.getChildren()[1]
                            .getProofNode();
                    System.err.println(
                            "[WARNING] Uncovered branching statement type: " + currentNode.getElementType());
                    // TODO
                } else if (currentNode instanceof IExecutionBranchStatement) {
                    // TODO
                    System.err.println(
                            "[WARNING] Uncovered branching statement type: " + currentNode.getElementType());
                } else {
                    // ...
                    // TODO Is there more to support?
                    System.err.println(
                            "[WARNING] Uncovered branching statement type: " + currentNode.getElementType());
                }

                currentNode = null;
            } else {
                // Store for later
                executionStack.push(currentNode);
                currentNode = currentNode.getChildren()[0];
            }
        }

        while ((currentNode = executionStack.pollFirst()) != null) {
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
                                    + typeRef.toString());
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
                                + app.rule().name());
            }
        } else {
            // TODO What other cases to support?
            System.err.println(
                    "[WARNING] Did not translate the following taclet app: "
                            + app.rule().name());
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
