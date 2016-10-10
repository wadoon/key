package de.tud.cs.se.ds.psec.compiler.ast;

import java.util.HashMap;
import java.util.List;
import java.util.Optional;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.exceptions.NoTranslationException;
import de.tud.cs.se.ds.psec.parser.ast.TranslationDefinition;
import de.tud.cs.se.ds.psec.parser.ast.TranslationDefinitions;
import de.tud.cs.se.ds.psec.util.InformationExtraction;
import de.tud.cs.se.ds.psec.util.Utilities;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.ContractRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Factory class for creating {@link TacletASTNode}s in course of the execution
 * of a particular method. Main methods are:
 * 
 * <ul>
 * <li>{@link #getTranslationForRuleApp(TacletApp)}<br>
 * returns a {@link TacletASTNode} for the given {@link TacletApp}.</li>
 * <li>{@link #getASTRootNode()}<br>
 * returns a root node for a taclet AST.</li>
 * </ul>
 *
 * @author Dominic Scheurer
 */
public class TacletTranslationFactory {
    private static final Logger logger = LogManager.getFormatterLogger();

    private MethodVisitor mv;
    private TranslationDefinitions definitions = null;
    private ProgVarHelper pvHelper;
    private Services services;

    /**
     * Creates a new {@link TacletTranslationFactory}.
     * 
     * @param mv
     *            The {@link MethodVisitor} used in compilation of the
     *            corresponding method.
     * @param pvHelper
     *            The {@link ProgVarHelper} for obtaining indices for program
     *            variables.
     * @param definitions
     *            TODO
     */
    public TacletTranslationFactory(MethodVisitor mv, ProgVarHelper pvHelper,
            TranslationDefinitions definitions, Services services) {
        super();
        this.mv = mv;
        this.pvHelper = pvHelper;
        this.definitions = definitions;
        this.services = services;
    }

    /**
     * Creates a root node for the AST.
     *
     * @return A root node for the AST.
     */
    public TacletASTNode getASTRootNode() {
        return new ASTRoot();
    }

    /**
     * Returns an {@link Optional} comprising a {@link TacletASTNode} for the
     * given {@link TacletApp}.
     *
     * @param app
     *            The {@link TacletApp} for which to create a translation
     *            object.
     * @return An {@link Optional} with a {@link TacletASTNode} for the given
     *         {@link TacletApp} or an empty {@link Optional} if there is no
     *         suitable such {@link TacletASTNode}.
     */
    public Optional<TacletASTNode> getTranslationForRuleApp(TacletApp app) {
        String ruleName = app.taclet().name().toString();
        logger.trace("Translating taclet %s", ruleName);

        TacletASTNode result = null;
        List<TranslationDefinition> candidates = definitions
                .getDefinitionsFor(ruleName);

        if (candidates != null) {
            RuleInstantiations instantiations = new RuleInstantiations(app);
            result = new TacletASTNode(ruleName, candidates, mv, pvHelper,
                    instantiations, services);
        } else {
            if (!isSimplificationSETaclet(app.taclet())) {
                String message = Utilities.format(
                        "Don't know a translation of the following rule app: %s",
                        ruleName);

                logger.error(message);
                throw new NoTranslationException(message);
            } else {
                logger.debug("Ignoring taclet %s", ruleName);
            }
        }

        return result == null ? Optional.empty() : Optional.of(result);
    }

    /**
     * Returns an {@link Optional} comprising a {@link TacletASTNode} for the
     * given {@link ContractRuleApp}.
     *
     * @param app
     *            The {@link ContractRuleApp} for which to create a translation
     *            object.
     * @return An {@link Optional} with a {@link TacletASTNode} for the given
     *         {@link ContractRuleApp} or an empty {@link Optional} if there is
     *         no suitable such {@link TacletASTNode}.
     */
    public Optional<TacletASTNode> getTranslationForRuleApp(
            ContractRuleApp app) {
        IProgramMethod pm = app.getRuleInstantiations().pm;
        logger.trace(
                "Instantiating translation of Operation Contract application for %s%s",
                pm.name().toString(),
                InformationExtraction.getMethodTypeDescriptor(pm));

        HashMap<String, Object> instantiations = new HashMap<>();
        instantiations.put("#pm", pm);
        instantiations.put("#actualSelf",
                pm.isStatic() ? null : (LocationVariable) app.getRuleInstantiations().actualSelf.op());
        instantiations.put("#actualParams",
                app.getRuleInstantiations().actualParams);
        instantiations.put("#actualResult",
                app.getRuleInstantiations().actualResult);

        return getTranslationForRuleApp(app.rule().name().toString(),
                instantiations);
    }

    /**
     * Returns an {@link Optional} comprising a {@link TacletASTNode} for the
     * {@link RuleApp} with the given <code>ruleName</code>.
     *
     * @param ruleName
     *            The name of the SE rule to translate.
     * @param instantiations
     *            The instantiations for constructs used by the
     *            {@link BuiltInRule}.
     * @return An {@link Optional} with a {@link TacletASTNode} for the given
     *         rule name or an empty {@link Optional} if there is no suitable
     *         such {@link TacletASTNode}.
     */
    private Optional<TacletASTNode> getTranslationForRuleApp(String ruleName,
            HashMap<String, Object> instantiations) {
        logger.trace("Translating rule %s", ruleName);

        TacletASTNode result = null;
        List<TranslationDefinition> candidates = definitions
                .getDefinitionsFor(ruleName);

        if (candidates != null) {

            result = new TacletASTNode(ruleName, candidates, mv, pvHelper,
                    new RuleInstantiations(instantiations), services);

        } else {
            String message = Utilities.format(
                    "Don't know a translation of the following taclet app: %s",
                    ruleName);

            logger.error(message);
            throw new NoTranslationException(message);
        }

        return result == null ? Optional.empty() : Optional.of(result);
    }

    /**
     * Checks whether a symbolic execution taclet is only simplifying the Java
     * expression and therefore may be ignored in compilation (there will be
     * further {@link TacletApp}s generated from those ignored
     * {@link TacletApp}s that are actually compiled).
     * <p>
     * 
     * We ignore a {@link Taclet} iff:
     * <ul>
     * <li>It has a <code>\replacewith</code> part generating exactly one new
     * sequent, <strong>and</strong></li>
     * <li>It does not change the symbolic state, i.e. the top level
     * {@link Operator} of the <code>\replacewith</code> part is
     * <strong>not</strong> an {@link UpdateApplication}.</li>
     * </ul>
     * 
     * @param taclet
     *            The {@link Taclet} to check.
     * @return true iff this {@link Taclet} may be ignored in compilation.
     */
    private static boolean isSimplificationSETaclet(Taclet taclet) {
        if (taclet.goalTemplates().size() != 1) {
            return false;
        }

        Operator replTermTopLevelOp = ((Term) taclet.goalTemplates().head()
                .replaceWithExpressionAsObject()).op();

        return !(replTermTopLevelOp instanceof UpdateApplication);
    }

    /**
     * Tries to return a {@link TacletASTNode} for the given SE taclet name. The
     * corresponding SE taclet may not depend on the instantiation of schema
     * variables!
     *
     * @param app
     *            The name of the {@link Taclet} to return a translation for.
     * @return An {@link Optional} with a {@link TacletASTNode} for the given
     *         {@link TacletApp} or an empty {@link Optional} if there is no
     *         suitable such {@link TacletASTNode}.
     */
    public Optional<TacletASTNode> getTranslationForTacletWithoutArgs(
            String tacletName) {
        logger.trace("Translating taclet %s", tacletName);

        TacletASTNode result = new TacletASTNode(tacletName,
                definitions.getDefinitionsFor(tacletName), mv, pvHelper, null,
                null);

        return result == null ? Optional.empty() : Optional.of(result);
    }
}

class MethodCalls {
    private int i;

    /*
     * @ public normal_behavior
     * 
     * @ requires true;
     * 
     * @ ensures true;
     * 
     * @
     */
    public MethodCalls(int i) {
        // TODO: Currently, we have to do an explicit super() call.
        // This should be done by the compiler if we omit it.
        super();

        this.i = i;
    }

    /*
     * @ public normal_behavior
     * 
     * @ requires true;
     * 
     * @ ensures true;
     * 
     * @
     */
    public boolean equals(Object o) {
        if (!(o instanceof MethodCalls)) {
            return false;
        }

        return equals((MethodCalls) o);
    }

    /*
     * @ public normal_behavior
     * 
     * @ requires true;
     * 
     * @ ensures true;
     * 
     * @
     */
    public boolean equals(MethodCalls o) {
        return i == o.i;
    }

}
