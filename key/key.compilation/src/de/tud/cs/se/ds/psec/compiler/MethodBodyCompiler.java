package de.tud.cs.se.ds.psec.compiler;

import java.util.Deque;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Optional;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.compiler.ast.TacletTranslationFactory;
import de.tud.cs.se.ds.psec.parser.ast.TranslationDefinitions;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.statement.EmptyStatement;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.util.Pair;

/**
 * Compiles the body of a method by Symbolic Execution.
 *
 * @author Dominic Scheurer
 */
public class MethodBodyCompiler implements Opcodes {
    private static final Logger logger = LogManager.getFormatterLogger();

    private String currentStatement;
    private ProgVarHelper pvHelper;
    private TacletTranslationFactory translationFactory;
    private TacletASTNode astRoot = null;
    private boolean isVoid = false;
    /**
     * Constructs a new {@link MethodBodyCompiler}.
     * 
     * @param mv
     *            The {@link MethodVisitor} to be used for compilation.
     * @param methodParameters
     *            The parameters of this method.
     * @param definitions
     *            TODO
     * @param isStatic
     *            true iff the method to be compiled is a static method, i.e.
     *            should have no "this" field as first local variable.
     * @param isVoid
     *            TODO
     */
    public MethodBodyCompiler(MethodVisitor mv,
            Iterable<ParameterDeclaration> methodParameters,
            TranslationDefinitions definitions, boolean isStatic,
            boolean isVoid) {
        this.pvHelper = new ProgVarHelper(isStatic, methodParameters);
        this.translationFactory = new TacletTranslationFactory(mv, pvHelper,
                definitions);
        this.isVoid = isVoid;

        methodParameters.forEach(p -> pvHelper
                .progVarNr(p.getVariables().get(0).getProgramVariable()));
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
        Node startNode = ffUntilAfterFirstMethodCall(builder);

        astRoot = translationFactory.getASTRootNode();
        translateToTacletTree(startNode, astRoot);

        if (isVoid) {
            addReturnAfterAllLeaves();
        }

        astRoot.compile();
    }

    /**
     * Adds a return instruction (for void methods) to all leaves in the AST
     * where there is not already one present.
     */
    private void addReturnAfterAllLeaves() {
        Deque<TacletASTNode> stack = new LinkedList<>();
        stack.push(astRoot);

        while (!stack.isEmpty()) {
            TacletASTNode currentNode = stack.pop();

            currentNode.children().forEach(child -> {
                if (child.children().size() == 0 && !(child.seTacletName()
                        .equals("methodCallEmptyReturn"))) {
                    // child is a leaf that is not a return
                    child.addChild(translationFactory
                            .getTranslationForTacletWithoutArgs(
                                    "methodCallEmptyReturn")
                            .get());
                }
                else {
                    stack.push(child);
                }
            });
        }
    }

    /**
     * "Fast-forwards" the tree until the first statement after the first method
     * call in the tree.
     *
     * @param builder
     *            {@link SymbolicExecutionTreeBuilder} resulting from execution
     *            of the method's body.
     * @return The {@link IExecutionNode} following the call to this method.
     */
    private Node ffUntilAfterFirstMethodCall(
            SymbolicExecutionTreeBuilder builder) {
        Node currentNode = builder.getStartNode().getProofNode();
        while (!(currentNode.getAppliedRuleApp().rule().name().toString().equals("methodBodyExpand"))) {
            currentNode = currentNode.child(0);
        }
        
        return currentNode.child(0);
    }

    /**
     * Translates the set with root <code>startNode</code> to a taclet AST,
     * where each node is a compilable {@link TacletASTNode}.
     *
     * @param startNode
     *            The root node for the SET to translate.
     * @param currentASTNode
     *            The root node for the corresponding taclet AST.
     */
    private void translateToTacletTree(Node currentNode,
            TacletASTNode currentASTNode) {

        // XXX Special case: "Use Operation Contract" has only one
        // *abstract* SET child, but two in the KeY proof tree. Have
        // to consider this. Maybe somehow deactivate all non-SE branches...

        Pair<Node, TacletASTNode> endNode = translateSequentialBlock(
                currentNode, currentASTNode);

        currentNode = endNode.first;
        currentASTNode = endNode.second;

        //XXX The following statement leads to an assertion error
        // when compilation is started from within a Junit test case.
//            currentStatement = currentNode.toString();
        
        if (currentNode.childrenCount() > 0) {

            // Note: Stack Map Frames are not generated manually here;
            // we're trying to leave it to the ASM framework to generate
            // them automatically. Computing the right values of these
            // frames is very difficult...
            // http://chrononsystems.com/blog/java-7-design-flaw-leads-to-huge-backward-step-for-the-jvm
            // http://asm.ow2.org/doc/developer-guide.html#classwriter

            Iterator<Node> childIt = currentNode.childrenIterator();
            while (childIt.hasNext()) {
                translateToTacletTree(childIt.next(), currentASTNode);
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
    private Pair<Node, TacletASTNode> translateSequentialBlock(Node currentProofNode,
            TacletASTNode astStartNode) {
        TacletASTNode astCurrentNode = astStartNode;

        do {
            RuleApp app = currentProofNode.getAppliedRuleApp();
            Optional<TacletASTNode> newNode = Optional.empty();
            if (hasNonEmptyActiveStatement(currentProofNode)) {
                newNode = toASTNode(app);
            }

            if (newNode.isPresent()) {
                astCurrentNode.addChild(newNode.get());
                astCurrentNode = newNode.get();
            }

            if (currentProofNode.childrenCount() == 1) {
                currentProofNode = currentProofNode.child(0);
            }else {
                // No children, or this is a branching node
                break;
            }
        }
        while (true);

        return new Pair<>(currentProofNode, astCurrentNode);
    }

    /**
     * Bridge to {@link TacletTranslationFactory} throwing an error if there is
     * an unexpected type of {@link RuleApp}.
     *
     * @param ruleApp
     *            The {@link RuleApp} to translate; usually a {@link TacletApp}.
     */
    private Optional<TacletASTNode> toASTNode(RuleApp ruleApp) {
        if (ruleApp instanceof TacletApp) {
            TacletApp app = (TacletApp) ruleApp;
            return translationFactory.getTranslationForTacletApp(app);
        }
        else {
            // TODO Are there other cases to support?
            logger.error(
                    "Did not translate the following app: %s, statement: %s",
                    ruleApp.rule().name(), currentStatement);
            System.exit(1);
            return Optional.empty();
        }
    }

    /**
     * Determines whether the given {@link Node} is a symbolic execution node in
     * the sense that it contains a non-empty active statement.
     *
     * @param node
     *            The {@link Node} to check.
     * @return true iff the given {@link Node} contains a non-empty active
     *         statement.
     */
    private static boolean hasNonEmptyActiveStatement(Node node) {
        SourceElement src = node.getNodeInfo().getActiveStatement();

        return src != null && !src.getClass().equals(EmptyStatement.class)
                && !(src instanceof StatementBlock
                        && ((StatementBlock) src).isEmpty());
    }
}
