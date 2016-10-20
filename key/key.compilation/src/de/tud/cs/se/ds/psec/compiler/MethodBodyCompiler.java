package de.tud.cs.se.ds.psec.compiler;

import java.util.Deque;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Optional;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.key_project.util.collection.ImmutableArray;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

import de.tud.cs.se.ds.psec.compiler.ast.DummyASTNode;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.compiler.ast.TacletTranslationFactory;
import de.tud.cs.se.ds.psec.compiler.exceptions.IncompleteSymbolicExecutionException;
import de.tud.cs.se.ds.psec.compiler.exceptions.NoTranslationException;
import de.tud.cs.se.ds.psec.parser.ast.TranslationDefinitions;
import de.tud.cs.se.ds.psec.util.InformationExtraction;
import de.tud.cs.se.ds.psec.util.Utilities;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.EmptyStatement;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.label.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.ContractRuleApp;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;

/**
 * Compiles the body of a method by Symbolic Execution.
 *
 * @author Dominic Scheurer
 */
public class MethodBodyCompiler implements Opcodes {
    private static final Logger logger = LogManager.getFormatterLogger();

    private ProgVarHelper pvHelper;
    private TacletTranslationFactory translationFactory;
    private TacletASTNode astRoot = null;
    private ProgramMethod mDecl;
    private MethodVisitor mv;

    /**
     * Constructs a new {@link MethodBodyCompiler}.
     * 
     * @param mDecl
     *            The {@link ProgramMethod} to translate.
     * @param mv
     *            The {@link MethodVisitor} to be used for compilation.
     * @param definitions
     *            The {@link TranslationDefinitions} to use for compilation.
     */
    public MethodBodyCompiler(ProgramMethod mDecl, MethodVisitor mv,
            TranslationDefinitions definitions, Services services) {
        this.mDecl = mDecl;
        this.mv = mv;
        ImmutableArray<ParameterDeclaration> methodParameters = mDecl
                .getParameters();
        this.pvHelper = new ProgVarHelper(mDecl.isStatic(), methodParameters);
        this.translationFactory = new TacletTranslationFactory(mDecl, mv,
                pvHelper, definitions, services);

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

        assertExecutionIsExhaustive(builder);

        // Forward until after call of this method
        Node startNode = ffUntilAfterFirstMethodCall(builder);

        // Add a super() call to the beginning of a constructor if there
        // is no explicit one. In Java, you can omit this, while in bytecode,
        // it is required.
        if (shouldAddConstructorCall(startNode)) {
            // TODO Check what happens if there is no super constructor with
            // empty arguments. Does KeY complain in this case, like the Java
            // compiler would?
            logger.info(
                    "There is no super constructor call in %s%s, adding one",
                    mDecl.name(),
                    InformationExtraction.getMethodTypeDescriptor(mDecl));
            addConstructorCall();
        }

        astRoot = translationFactory.getASTRootNode();
        translateToTacletTree(startNode, astRoot);

        if (mDecl.isVoid() || mDecl.isConstructor()) {
            addReturnAfterAllLeaves();
        }

        astRoot.compile();
    }

    /**
     * Adds a call to the standard constructor of the super type of the
     * {@link ProgramMethod}.
     */
    private void addConstructorCall() {
        mv.visitVarInsn(ALOAD, 0);
        mv.visitMethodInsn(INVOKESPECIAL, InformationExtraction.getExtending(
                (TypeDeclaration) mDecl.getContainerType().getJavaType()),
                "<init>", "()V", false);
    }

    /**
     * Checks whether we should add a super call before beginning the
     * translation of the actual {@link ProgramMethod} body; this is true iff
     * the {@link ProgramMethod} is a constructor and the first statement to be
     * compiled is not a super call.
     * 
     * @param startNode
     *            The first {@link Node} in the {@link Proof} that should be
     *            translated.
     * @return True iff the {@link ProgramMethod} is a constructor and the first
     *         statement to be compiled, given by the supplied {@link Node}, is
     *         not a super call.
     */
    private boolean shouldAddConstructorCall(Node startNode) {
        if (!mDecl.isConstructor()) {
            return false;
        }

        if (startNode.getAppliedRuleApp() == null) {
            // If the rule app is null, we also need to add a constructor -- in
            // this case, the constructor body is actually empty
            return true;
        }

        SourceElement actStmt = NodeInfo
                .computeActiveStatement(startNode.getAppliedRuleApp());

        if (actStmt == null || !(actStmt instanceof MethodReference)) {
            return true;
        }

        MethodReference mRef = (MethodReference) actStmt;

        return !mRef.getName().equals("<init>");
    }

    /**
     * Checks if all leaves in the SE tree don't contain a non-empty
     * {@link JavaBlock}; otherwise, an
     * {@link IncompleteSymbolicExecutionException} is thrown.
     * 
     * @param builder
     *            The {@link SymbolicExecutionTreeBuilder} to extract the proof
     *            tree from.
     * @throws IncompleteSymbolicExecutionException
     *             if there is a leaf in the tree that still contains some Java
     *             code.
     */
    private void assertExecutionIsExhaustive(
            SymbolicExecutionTreeBuilder builder) {
        builder.getProof().openGoals().forEach(g -> {
            g.node().sequent().succedent().forEach(f -> {
                JavaBlock block = JoinRuleUtils
                        .getJavaBlockRecursive(f.formula());
                if (!block.equals(JavaBlock.EMPTY_JAVABLOCK)) {
                    String msg = Utilities.format(
                            "Symbolic execution was not exhaustive; "
                                    + "is there an error in the program?\nProblem in method %s:\n%s",
                            InformationExtraction.getMethodDescriptor(mDecl),
                            JavaTools.getActiveStatement(block));
                    throw new IncompleteSymbolicExecutionException(msg);
                }
            });
        });
    }

    /**
     * Adds a return instruction (for void methods) to all leaves in the AST
     * where there is not already one present.
     */
    private void addReturnAfterAllLeaves() {
        if (astRoot.children().isEmpty()) {
            // This is obviously an empty method, like a private
            // standard constructor for a Singleton.
            astRoot.addChild(translationFactory
                    .getTranslationForTacletWithoutArgs("methodCallEmptyReturn")
                    .get());
            return;
        }

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
                } else {
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

        while (!(currentNode.getAppliedRuleApp().rule().name().toString()
                .equals("methodBodyExpand"))) {
            currentNode = currentNode.child(0);
        }

        currentNode = currentNode.child(0);

        while (currentNode.childrenCount() == 1 && !currentNode.leaf()
                && !translationFactory.assertHasDefinitionFor(
                        currentNode.getAppliedRuleApp())) {
            currentNode = currentNode.child(0);
        }

        return currentNode;
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

        Pair<Node, TacletASTNode> endNode = translateSequentialBlock(
                currentNode, currentASTNode);

        currentNode = endNode.first;
        currentASTNode = endNode.second;

        if (currentNode.childrenCount() > 0) {

            // We only compile as many children as are called in the
            // TranslationDefinitions. Translations may decide to explicitly
            // ignore certain subbranches.

            final int maxIndexOfChildrenCallsInTranslations = currentASTNode
                    .maxNumberOfChildrenCallsInTranslations();

            // Note: Stack Map Frames are not generated manually here;
            // we're trying to leave it to the ASM framework to generate
            // them automatically. Computing the right values of these
            // frames is very difficult...
            // http://chrononsystems.com/blog/java-7-design-flaw-leads-to-huge-backward-step-for-the-jvm
            // http://asm.ow2.org/doc/developer-guide.html#classwriter

            int cnt = 0;
            Iterator<Node> childIt = currentNode.childrenIterator();
            while (childIt.hasNext()
                    && cnt < maxIndexOfChildrenCallsInTranslations) {
                cnt++;

                Node nextChild = childIt.next();

                if (nextChild.isClosed()) {
                    logger.trace(
                            "Closed branch \"%s\" in the SET, adding dummy node",
                            nextChild.getNodeInfo().getBranchLabel());
                    currentASTNode.addChild(new DummyASTNode());
                } else {
                    translateToTacletTree(nextChild, currentASTNode);
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
    private Pair<Node, TacletASTNode> translateSequentialBlock(
            Node currentProofNode, TacletASTNode astStartNode) {
        TacletASTNode astCurrentNode = astStartNode;

        do {
            RuleApp app = currentProofNode.getAppliedRuleApp();
            Optional<TacletASTNode> newNode = Optional.empty();

            if (isSymbolicExecutionNode(currentProofNode)
                    && isAddressingMainModality(currentProofNode, app)) {
                newNode = toASTNode(app);
            }

            if (newNode.isPresent()) {
                astCurrentNode.addChild(newNode.get());
                astCurrentNode = newNode.get();
            }

            if (currentProofNode.childrenCount() == 1) {
                currentProofNode = currentProofNode.child(0);
            } else {
                // No children, or this is a branching node
                break;
            }
        } while (true);

        return new Pair<>(currentProofNode, astCurrentNode);
    }

    /**
     * Checks whether the given {@link RuleApp} addresses the {@link Modality}
     * with the highest {@link SymbolicExecutionTermLabel}, which is usually the
     * one that we want to compile.
     * 
     * @param currentProofNode
     *            The current {@link Proof} {@link Node} on which the
     *            {@link RuleApp} is applied.
     * @param app
     *            The {@link RuleApp} for which we should check whether the
     *            right {@link Modality} is addressed.
     * @return true iff the modality with the highest
     *         {@link SymbolicExecutionTermLabel} is addressed by the
     *         {@link RuleApp}.
     */
    private static boolean isAddressingMainModality(Node currentProofNode,
            RuleApp app) {
        // Find the relevant modality
        PosInOccurrence outerModalityPio = SymbolicExecutionUtil
                .findModalityWithMaxSymbolicExecutionLabelId(
                        currentProofNode.sequent());

        // Go below updates
        while (outerModalityPio.subTerm().op() instanceof UpdateApplication) {
            outerModalityPio = outerModalityPio.down(1);
        }

        // This should now really have a JavaBlock
        assert !outerModalityPio.subTerm().javaBlock().isEmpty();

        // Check whether the rule app does not address a wrong JavaBlock
        PosInTerm ruleAppPit = app.posInOccurrence().posInTerm();
        
        return ruleAppPit.isTopLevel()
                || outerModalityPio.posInTerm().equals(ruleAppPit);
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
            return translationFactory
                    .getTranslationForRuleApp((TacletApp) ruleApp);
        } else if (ruleApp instanceof ContractRuleApp) {
            return translationFactory
                    .getTranslationForRuleApp((ContractRuleApp) ruleApp);
        } else if (ruleApp instanceof LoopInvariantBuiltInRuleApp) {
            return translationFactory.getTranslationForRuleApp(
                    (LoopInvariantBuiltInRuleApp) ruleApp);
        } else if (ruleApp instanceof OneStepSimplifierRuleApp) {
            // This can be ignored
            return Optional.empty();
        } else {
            String message = Utilities.format(
                    "Unsupported rule application: %s", ruleApp.rule().name());
            throw new NoTranslationException(message);
        }
    }

    /**
     * Determines whether the given {@link Node} is a symbolic execution node,
     * which is true if it either has a non-empty active statement (the
     * {@link RuleApp} is a {@link PosTacletApp}) or it is an application of the
     * operation contract rule.
     *
     * @param node
     *            The {@link Node} to check.
     * @return true iff the given {@link Node} is a symbolic execution
     *         {@link Node}.
     */
    private static boolean isSymbolicExecutionNode(Node node) {
        return !(node.getAppliedRuleApp() instanceof OneStepSimplifierRuleApp)
                && (hasNonEmptyActiveStatement(node) || node
                        .getAppliedRuleApp() instanceof AbstractBuiltInRuleApp);
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
