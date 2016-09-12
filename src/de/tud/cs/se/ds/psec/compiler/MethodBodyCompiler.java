package de.tud.cs.se.ds.psec.compiler;

import java.util.ArrayDeque;
import java.util.Deque;

import org.objectweb.asm.MethodVisitor;

import de.uka.ilkd.key.java.statement.IGuard;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopInvariant;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * Compiles the body of a method by Symbolic Execution.
 *
 * @author Dominic Scheurer
 */
public class MethodBodyCompiler {
    private MethodVisitor mv;

    /**
     * TODO
     * 
     * @param mv
     */
    public MethodBodyCompiler(MethodVisitor mv) {
        this.mv = mv;
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
                    
                    Node preservesInvBranch = loopInvNode.getChildren()[0].getProofNode();
                    Node useCaseBranch = loopInvNode.getChildren()[1].getProofNode();
                    // TODO
                } else if (currentNode instanceof IExecutionBranchStatement) {
                    // TODO
                } else {
                    //...
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
            System.out.println(currentNode);
        }
    }
}
