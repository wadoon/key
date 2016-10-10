package de.tud.cs.se.ds.psec.compiler.ast;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Collectors;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.exceptions.UnexpectedTranslationSituationException;
import de.tud.cs.se.ds.psec.parser.ast.ApplicabilityCheckInput;
import de.tud.cs.se.ds.psec.parser.ast.TranslationDefinition;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.tud.cs.se.ds.psec.util.Utilities;
import de.uka.ilkd.key.java.Services;
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
    private RuleInstantiations instantiations;
    private List<TranslationDefinition> definitions;
    private String seTacletName;
    private Services services;

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
     * @param instantiations
     *            TODO
     * @see TacletTranslationFactory
     */
    public TacletASTNode(String seTacletName,
            List<TranslationDefinition> definitions, MethodVisitor mv,
            ProgVarHelper pvHelper, RuleInstantiations instantiations,
            Services services) {
        this.instantiations = instantiations;
        this.mv = mv;
        this.pvHelper = pvHelper;
        this.definitions = definitions;
        this.seTacletName = seTacletName;
        this.services = services;
    }

    /**
     * Recursively translates this node and its children to bytecode.
     * 
     * @throws UnexpectedTranslationSituationException
     *             if not exactly one {@link TranslationDefinition} is
     *             applicable in the present situation.
     */
    public void compile() throws UnexpectedTranslationSituationException {
        logger.trace("Compiling %s", seTacletName);

        // We allow the app to be null; this may happen e.g. in calls to
        // TacletTranslationFactory#getTranslationForTacletWithoutArgs(String).
        // If this is actually caused by an error, there will be a succeeding
        // NullPointerException during the applicability check.
        ApplicabilityCheckInput applCheckInput = new ApplicabilityCheckInput(
                children.size(), instantiations, services);

        List<TranslationDefinition> candidates = definitions.stream()
                .filter(d -> d.isApplicable(applCheckInput))
                .collect(Collectors.toList());

        if (candidates.size() < 1) {
            String message = Utilities.format(
                    "No suitable translation found for the situation %s",
                    applCheckInput);

            logger.error(message);
            throw new UnexpectedTranslationSituationException(message);
        } else if (candidates.size() > 1) {
            String message = Utilities.format(
                    "Too many translations (%s) found for the situation %s",
                    candidates.size(), applCheckInput);
            logger.error(message);
            throw new UnexpectedTranslationSituationException(message);
        }

        UniqueLabelManager labelManager = new UniqueLabelManager();

        logger.trace("Using translation %s",
                candidates.get(0).getTranslationName());

        candidates.get(0).translate(mv, pvHelper, labelManager, instantiations,
                services, children);
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
     * @return The maximum number of children calls in the
     *         {@link TranslationDefinition}s supplied to this
     *         {@link TacletASTNode}.
     */
    public int maxNumberOfChildrenCallsInTranslations() {
        return definitions.stream()
                .map(TranslationDefinition::numberOfChildrenCalls)
                .collect(Collectors.maxBy(Comparator.naturalOrder())).get();
    }

    /**
     * Recursively compiles the first child of this AST node.
     * 
     * @throws UnexpectedTranslationSituationException
     *             if not exactly one {@link TranslationDefinition} is
     *             applicable in the present situation for the first child.
     */
    protected void compileFirstChild()
            throws UnexpectedTranslationSituationException {
        if (!children.isEmpty()) {
            children.get(0).compile();
        }
    }

}
