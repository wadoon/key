package de.tud.cs.se.ds.psec.compiler.ast;

import java.util.ArrayList;
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
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.ContractRuleApp;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.rule.PosTacletApp;
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
    private ProgramMethod methodBeingCompiled = null;
    private Services services;

    /**
     * Creates a new {@link TacletTranslationFactory}.
     * 
     * @param methonBeingCompiled
     *            TODO
     * @param mv
     *            The {@link MethodVisitor} used in compilation of the
     *            corresponding method.
     * @param pvHelper
     *            The {@link ProgVarHelper} for obtaining indices for program
     *            variables.
     * @param definitions
     *            The {@link TranslationDefinitions} containing the available
     *            translations.
     * @param services
     *            The {@link Services} object.
     */
    public TacletTranslationFactory(ProgramMethod methonBeingCompiled,
            MethodVisitor mv, ProgVarHelper pvHelper,
            TranslationDefinitions definitions, Services services) {
        this.methodBeingCompiled = methonBeingCompiled;
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
     * Checks whether there is an available {@link TranslationDefinition} for
     * the given {@link RuleApp}, or the {@link RuleApp} is in fact a
     * {@link TacletApp} for a simplification {@link Taclet}.
     * 
     * @param app
     *            The {@link RuleApp} to check for the availability of
     *            {@link TranslationDefinition}s.
     * @return true iff there is a {@link TranslationDefinition} for the given
     *         {@link RuleApp}, or the {@link RuleApp} is in fact a
     *         {@link TacletApp} for a simplification {@link Taclet}.
     * @throws NoTranslationException
     *             If there is no suitable translation and the {@link RuleApp}
     *             is not a simplification {@link TacletApp}.
     */
    public boolean assertHasDefinitionFor(RuleApp app) {
        int result = 0;

        if (app instanceof TacletApp) {
            TacletApp tacletApp = (TacletApp) app;

            String tacletName = tacletApp.taclet().name().toString();
            ArrayList<TranslationDefinition> availableDefinitions = definitions
                    .getDefinitionsFor(tacletName);
            if (availableDefinitions == null
                    || availableDefinitions.size() < 1) {
                if (isSimplificationSETaclet(tacletApp.taclet())) {
                    result = 0;
                } else {
                    result = -1;
                }
            } else {
                result = 1;
            }
        } else {
            if (app instanceof OneStepSimplifierRuleApp) {
                return false;
            }

            String ruleName = app.rule().name().toString();
            ArrayList<TranslationDefinition> availableDefinitions = definitions
                    .getDefinitionsFor(ruleName);
            if (availableDefinitions == null
                    || availableDefinitions.size() < 1) {
                result = -1;
            } else {
                result = 1;
            }
        }

        if (result == 0) {
            return false;
        } else if (result == 1) {
            return true;
        } else {
            String message = Utilities.format(
                    "Don't know a translation of the following rule: \"%s\" (App \"%s\")",
                    app.rule().name().toString(), app.getClass());

            logger.error(message);
            throw new NoTranslationException(message);
        }
    }

    /**
     * Returns an {@link Optional} comprising a {@link TacletASTNode} for the
     * given {@link TacletApp}.
     *
     * @param app
     *            The {@link TacletApp} for which to create a translation
     *            object.
     * @param statement
     * @return An {@link Optional} with a {@link TacletASTNode} for the given
     *         {@link TacletApp} or an empty {@link Optional} if there is no
     *         suitable such {@link TacletASTNode}.
     */
    public Optional<TacletASTNode> getTranslationForRuleApp(TacletApp app,
            String statement) {
        String ruleName = app.taclet().name().toString();
        logger.trace("Translating taclet %s", ruleName);

        TacletASTNode result = null;
        List<TranslationDefinition> candidates = definitions
                .getDefinitionsFor(ruleName);

        if (candidates != null) {
            RuleInstantiations instantiations = new RuleInstantiations(app);

            // TODO Check that the following update-extraction code works
            Optional<Term> maybeUpdate = Optional.empty();
            if (app instanceof PosTacletApp) {
                Term formula = ((PosTacletApp) app).posInOccurrence()
                        .sequentFormula().formula();

                maybeUpdate = extractUpdate(formula);
            }

            result = new TacletASTNode(ruleName, statement, candidates, mv,
                    pvHelper, instantiations, maybeUpdate, services);
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
     * TODO
     * 
     * @param formula
     * @return
     */
    private Optional<Term> extractUpdate(Term formula) {
        Optional<Term> maybeUpdate;
        if (formula.op() instanceof UpdateApplication) {
            maybeUpdate = Optional.of(formula.sub(0));
        } else {
            maybeUpdate = Optional.empty();
        }
        return maybeUpdate;
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
    public Optional<TacletASTNode> getTranslationForRuleApp(ContractRuleApp app,
            String statement) {
        IProgramMethod pm = app.getRuleInstantiations().pm;
        logger.trace(
                "Instantiating translation of Operation Contract application for %s%s",
                pm.name().toString(),
                InformationExtraction.getMethodTypeDescriptor(pm));

        HashMap<String, Object> instantiations = new HashMap<>();
        instantiations.put("#methodBeingCompiled", methodBeingCompiled);
        instantiations.put("#pm", pm);
        instantiations.put("#containerType", pm.getContainerType());
        instantiations.put("#actualSelf",
                pm.isStatic()
                        || app.getRuleInstantiations().actualSelf == null
                                ? null
                                : (LocationVariable) app
                                        .getRuleInstantiations().actualSelf
                                                .op());
        instantiations.put("#actualParams",
                app.getRuleInstantiations().actualParams);
        instantiations.put("#actualResult",
                app.getRuleInstantiations().actualResult);

        // TODO Check if update extraction works!
        return getTranslationForRuleApp(app.rule().name().toString(),
                instantiations, extractUpdate(app.programTerm()), statement);
    }

    /**
     * Translates a {@link LoopInvariantBuiltInRuleApp} to a
     * {@link TacletASTNode}.
     * 
     * @param app
     *            The {@link LoopInvariantBuiltInRuleApp} to translate.
     * @param statement
     *            The Java statement being translated.
     * @return The translation.
     */
    public Optional<TacletASTNode> getTranslationForRuleApp(
            LoopInvariantBuiltInRuleApp app, String statement) {
        logger.trace(
                "Instantiating translation of Loop Invariant application for %s",
                statement);

        HashMap<String, Object> instantiations = new HashMap<>();
        instantiations.put("#guard", app.getGuard());

        return getTranslationForRuleApp(app.rule().name().toString(),
                instantiations, Optional.empty(), statement);
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
     * @param update
     *            TODO
     * @param statement
     *            The Java statement being translated.
     * @return An {@link Optional} with a {@link TacletASTNode} for the given
     *         rule name or an empty {@link Optional} if there is no suitable
     *         such {@link TacletASTNode}.
     */
    private Optional<TacletASTNode> getTranslationForRuleApp(String ruleName,
            HashMap<String, Object> instantiations, Optional<Term> update,
            String statement) {
        logger.trace("Translating rule %s", ruleName);

        TacletASTNode result = null;
        List<TranslationDefinition> candidates = definitions
                .getDefinitionsFor(ruleName);

        if (candidates != null) {

            result = new TacletASTNode(ruleName, statement, candidates, mv,
                    pvHelper, new RuleInstantiations(instantiations), update,
                    services);

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
     * TODO: This method is probably not precise enough, there could be false
     * positives; for instance, break statements would be ignored... We should
     * try to better capture the concept of a rewriting rule.
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

        TacletASTNode result = new TacletASTNode(tacletName, "",
                definitions.getDefinitionsFor(tacletName), mv, pvHelper, null,
                null, null);

        return result == null ? Optional.empty() : Optional.of(result);
    }
}
