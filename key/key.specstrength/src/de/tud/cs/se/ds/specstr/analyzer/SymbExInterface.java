// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.tud.cs.se.ds.specstr.analyzer;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.key_project.util.collection.ImmutableSet;

import de.tud.cs.se.ds.specstr.profile.StrengthAnalysisSEProfile;
import de.tud.cs.se.ds.specstr.strategy.StrengthAnalysisStrategy;
import de.tud.cs.se.ds.specstr.util.GeneralUtilities;
import de.tud.cs.se.ds.specstr.util.JavaTypeInterface;
import de.tud.cs.se.ds.specstr.util.LogicUtilities;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.macros.FinishSymbolicExecutionMacro;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.rule.LoopScopeInvariantRule;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.strategy.StrategyProperties;

/**
 * Bridge to KeY's symbolic execution engine.
 *
 * @author Dominic Steinhoefel
 */
public class SymbExInterface {
    /**
     * The {@link Logger} for this class.
     */
    private static final Logger LOGGER = LogManager.getFormatterLogger();

    /**
     * The {@link KeYEnvironment} for the method to analyze.
     */
    private KeYEnvironment<DefaultUserInterfaceControl> env;

    /**
     * The {@link File} containing the method to analyze.
     */
    private File file;

    /**
     * The constructed {@link Proof} object.
     */
    private Proof proof;

    /**
     * Constructor.
     *
     * @param file
     *            The {@link File} containing the method to analyze.
     * @throws ProblemLoaderException
     *             If the {@link File} could not be loaded, e.g. due to syntax
     *             errors.
     */
    public SymbExInterface(File file) throws ProblemLoaderException {
        this.file = file;
        initializeKeYEnv();
    }

    /**
     * Constructor.
     *
     * @param file
     *            The {@link File} containing the method to analyze.
     * @param env
     *            The {@link KeYEnvironment} for the problem to analyse (based
     *            on the {@link StrengthAnalysisSEProfile}).
     * @throws ProblemLoaderException
     *             If the {@link File} could not be loaded, e.g. due to syntax
     *             errors.
     */
    public SymbExInterface(File file,
            KeYEnvironment<DefaultUserInterfaceControl> env)
            throws ProblemLoaderException {
        this.file = file;
        this.env = env;
    }

    /**
     * Builds the {@link KeYEnvironment} for the problem to analyse (based on
     * the {@link StrengthAnalysisSEProfile}).
     *
     * @throws ProblemLoaderException
     *             If the {@link File} could not be loaded, e.g. due to syntax
     *             errors.
     */
    private void initializeKeYEnv() throws ProblemLoaderException {
        LOGGER.trace("Building KeY environment for file %s", file);
        // @formatter:off
        env = KeYEnvironment.load(
                StrengthAnalysisSEProfile.INSTANCE,
                file, // location
                null, // class path
                null, // boot class path
                null, // includes
                true); // forceNewProfileOfNewProofs
        // @formatter:on
        LOGGER.trace("Built up environment.");
    }

    /**
     * @see JavaTypeInterface#getDeclaredTypes(KeYEnvironment)
     * @return The {@link KeYJavaType}s declared in the {@link KeYEnvironment}.
     */
    public List<KeYJavaType> getDeclaredTypes() {
        return JavaTypeInterface.getDeclaredTypes(env);
    }

    /**
     * @return The {@link KeYEnvironment} object.
     */
    public KeYEnvironment<DefaultUserInterfaceControl> keyEnvironment() {
        return env;
    }

    /**
     * @return The {@link Proof} object if already initialized; make sure to
     *         call {@link #finishSEForMethod(ProgramMethod)} before calling
     *         this method.
     */
    public Proof proof() {
        return proof;
    }

    /**
     * Initializes the {@link Proof} for the given {@link IProgramMethod}.
     *
     * @param pm
     *            The {@link IProgramMethod} to analyze.
     * @see #setupStrategy(Proof)
     */
    private void initProof(ProgramMethod pm) {
        if (proof != null) {
            return;
        }

        final ImmutableSet<Contract> contracts = env
                .getSpecificationRepository()
                .getContracts(pm.getContainerType(), pm);

        if (contracts == null || contracts.size() != 1) {
            final String msg = GeneralUtilities.format(
                    "Expected 1 contract for method %s, found %s",
                    pm.getFullName(),
                    contracts == null ? 0 : contracts.size());

            LOGGER.error(msg);
            throw new RuntimeException(msg);
        }

        final Contract contract = contracts.iterator().next();
        assert contract instanceof FunctionalOperationContract;

        try {
            final FunctionalOperationContractPO po = //
                    new FunctionalOperationContractPO(//
                            env.getInitConfig(), //
                            (FunctionalOperationContract) contract, //
                            true, // add uninterpreted predicate
                            true); // add symbolic execution label

            proof = env.createProof(po);
            setupStrategy(proof);
        }
        catch (ProofInputException e) {
            GeneralUtilities.logErrorAndThrowRTE(LOGGER,
                    "Exception at '%s' of %s:\n%s", contract.getDisplayName(),
                    contract.getTarget(), e.getMessage());
        }
    }

    /**
     * Initializes the {@link Proof} for pm and finishes symbolic execution.
     *
     * @param pm
     *            The {@link ProgramMethod} to analyze.
     */
    public void finishSEForMethod(ProgramMethod pm) {
        initProof(pm);

        // Start auto mode
        finishSEForNode(proof.root());
    }

    /**
     * Finishes symbolic execution starting at the given {@link Node}.
     *
     * @param node
     *            The {@link Node} to start symbolic execution at.
     */
    private void finishSEForNode(Node node) {
        List<Node> openNodesWithModality = LogicUtilities
                .extractOpenNodesWithModality(node);
        List<Node> lastNodesWithModality = new ArrayList<>();

        while (!openNodesWithModality.isEmpty()
                && !openNodesWithModality.equals(lastNodesWithModality)) {

            openNodesWithModality.forEach(n -> {
                applyMacro(new FinishSymbolicExecutionMacro(), n);
            });

            lastNodesWithModality = new ArrayList<>(openNodesWithModality);

            openNodesWithModality = LogicUtilities
                    .extractOpenNodesWithModality(node);
        }
    }

    /**
     * Applies the given {@link ProofMacro} exhaustively, i.e. until it does not
     * change anything anymore.
     *
     * @param macro
     *            The {@link ProofMacro} to apply.
     * @param node
     *            The root of the subtree to apply the {@link ProofMacro} to.
     */
    public void applyMacroExhaustively(ProofMacro macro, Node node) {
        List<Node> openNodes = GeneralUtilities
                .toStream(node.proof().getSubtreeGoals(node)).map(g -> g.node())
                .collect(Collectors.toList());
        List<Node> lastNodes = new ArrayList<>();

        while (!openNodes.equals(lastNodes)) {
            openNodes.forEach(n -> applyMacro(macro, n));
            lastNodes = new ArrayList<>(openNodes);

            openNodes = GeneralUtilities
                    .toStream(node.proof().getSubtreeGoals(node))
                    .map(g -> g.node()).collect(Collectors.toList());
        }
    }

    /**
     * Applies a {@link ProofMacro} on a given {@link Node}.
     *
     * @param macro
     *            The {@link ProofMacro} to apply.
     * @param node
     *            The {@link Node} to apply the macro on.
     */
    public void applyMacro(ProofMacro macro, Node node) {
        try {
            macro.applyTo(env.getUi(), node, null, env.getUi());
        }
        catch (Exception e) {
            GeneralUtilities.logErrorAndThrowRTE(LOGGER,
                    "Problem in applying macro, message: %s", e.getMessage());
        }
    }

    /**
     * Finds all loop scope index variables in the {@link Proof} subtree
     * starting at the given {@link Node}.
     *
     * @param node
     *            To root of the subtree to search.
     * @return All loop scope index variables in the {@link Proof} subtree
     *         starting at the given {@link Node}.
     * @see LoopScopeInvariantRule
     */
    public static List<LocationVariable> findLoopScopeIndeces(final Node node) {
        final Proof proof = node.proof();
        List<LocationVariable> result = new ArrayList<>();

        for (Goal g : proof.getSubtreeGoals(node)) {
            for (SequentFormula sf : g.node().sequent().succedent()) {
                result.addAll(LogicUtilities.retrieveLoopScopeIndices(
                        new PosInOccurrence(sf, PosInTerm.getTopLevel(), false),
                        proof.getServices()));
            }
        }

        return result;
    }

    /**
     * Sets up the default strategy settings for strength analysis in the given
     * {@link Proof}.
     *
     * @param proof
     *            The {@link Proof} to set up.
     */
    private static void setupStrategy(Proof proof) {
        // Set proof strategy options
        final StrategyProperties sp = strategyProperties(proof);

        // Make sure that the new options are used
        int maxSteps = 10000;
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings()
                .setMaxSteps(maxSteps);
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings()
                .setActiveStrategyProperties(sp);
        proof.getSettings().getStrategySettings().setMaxSteps(maxSteps);
        proof.setActiveStrategy(
                new StrengthAnalysisStrategy.Factory().create(proof, sp));
    }

    /**
     * Sets and returns the {@link StrategyProperties} for strength analysis.
     *
     * @param proof
     *            The {@link Proof} the strategy of which to set.
     * @return The {@link StrategyProperties} for strength analysis.
     */
    private static StrategyProperties strategyProperties(Proof proof) {
        final StrategyProperties sp;
        sp = proof.getSettings().getStrategySettings()
                .getActiveStrategyProperties();

        // @formatter:off
        sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY,
                StrategyProperties.METHOD_CONTRACT);
        sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY,
                StrategyProperties.DEP_ON);
        sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY,
                StrategyProperties.QUERY_ON);
        sp.setProperty(
                StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY,
                StrategyProperties.NON_LIN_ARITH_DEF_OPS);
        sp.setProperty(
                StrategyProperties.STOPMODE_OPTIONS_KEY,
                StrategyProperties.STOPMODE_NONCLOSE);
        sp.setProperty(
                StrategyProperties.LOOP_OPTIONS_KEY,
                StrategyProperties.LOOP_SCOPE_INVARIANT);
        sp.setProperty(StrategyProperties.OSS_OPTIONS_KEY,
                StrategyProperties.OSS_OFF);
        // @formatter:on

        proof.getSettings().getStrategySettings()
                .setActiveStrategyProperties(sp);

        return sp;
    }
}
