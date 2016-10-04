package de.tud.cs.se.ds.psec.compiler.ast;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.parser.ast.ApplicabilityCheckInput;
import de.tud.cs.se.ds.psec.parser.ast.TranslationDefinition;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Models a symbolic execution taclet and offers a method for translating it
 * into bytecode.
 *
 * @author Dominic Scheurer
 */
public class TacletASTNode implements Opcodes {
    private static final Logger logger = LogManager.getFormatterLogger();

    private List<TacletASTNode> children = new ArrayList<>();
    private MethodVisitor mv;
    private ProgVarHelper pvHelper;
    private TacletApp app;
    private List<TranslationDefinition> definitions;
    private String seTacletName;

    /**
     * Constructs a new {@link TacletASTNode} for a given {@link TacletApp}.
     * 
     * @param seTacletName
     *            The name of the SE taclet being translated.
     * @param definitions
     *            The {@link TranslationDefinition}s for the corresponding SE
     *            taclet.
     * @param mv
     *            The {@link MethodVisitor} for compiling the
     *            {@link TacletASTNode}.
     * @param pvHelper
     *            The {@link ProgVarHelper} of the corresponding method.
     * @param app
     *            The {@link TacletApp} to construct this {@link TacletASTNode}
     *            from.
     * 
     * @see TacletTranslationFactory
     */
    public TacletASTNode(String seTacletName,
            List<TranslationDefinition> definitions, MethodVisitor mv,
            ProgVarHelper pvHelper, TacletApp app) {
        this.app = app;
        this.mv = mv;
        this.pvHelper = pvHelper;
        this.definitions = definitions;
        this.seTacletName = seTacletName;
    }

    /**
     * Recursively translates this node and its children to bytecode.
     */
    public void compile() {
        logger.trace("Compiling %s", seTacletName);
        
        ApplicabilityCheckInput applCheckInput = new ApplicabilityCheckInput(
                children.size());

        List<TranslationDefinition> candidates = definitions.stream()
                .filter(d -> d.isApplicable(applCheckInput))
                .collect(Collectors.toList());

        if (candidates.size() < 1) {
            logger.error("No suitable translation found for the situation %s",
                    applCheckInput);
            System.exit(1);
        }
        else if (candidates.size() > 1) {
            logger.error(
                    "Too many translations (%s) found for the situation %s",
                    candidates.size(), applCheckInput);
            System.exit(1);
        }
        
        UniqueLabelManager labelManager = new UniqueLabelManager();

        candidates.get(0).translate(mv, pvHelper, labelManager, app, children);
    }

    /**
     * @return The {@link MethodVisitor} for compiling this
     *         {@link TacletASTNode} to bytecode.
     */
    protected MethodVisitor mv() {
        return mv;
    }

    /**
     * @return The {@link ProgVarHelper} of the corresponding method.
     */
    protected ProgVarHelper pvHelper() {
        return pvHelper;
    }

    /**
     * @return The {@link TacletApp} for this {@link TacletASTNode}.
     */
    protected TacletApp app() {
        return app;
    }

    /**
     * @return The children of this {@link TacletASTNode}.
     */
    public List<TacletASTNode> children() {
        return children;
    }

    /**
     * Adds a child to this {@link TacletASTNode}.
     * 
     * @param child
     *            The {@link TacletASTNode} to add as a child to the current
     *            one.
     */
    public void addChild(TacletASTNode child) {
        children.add(child);
    }

    /**
     * @return The name of the symbolic execution taclet that is represented by
     *         this {@link TacletASTNode}.
     */
    public String seTacletName() {
        return seTacletName;
    }

    /**
     * Recursively compiles the first child of this AST node.
     */
    protected void compileFirstChild() {
        if (!children.isEmpty()) {
            children.get(0).compile();
        }
    }

}
