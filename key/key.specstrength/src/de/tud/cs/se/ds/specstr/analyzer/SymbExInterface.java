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
import java.util.List;
import java.util.stream.Collectors;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.key_project.util.collection.ImmutableSet;

import de.tud.cs.se.ds.specstr.util.InformationExtraction;
import de.tud.cs.se.ds.specstr.util.Utilities;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.macros.AbstractProofMacro;
import de.uka.ilkd.key.macros.FinishSymbolicExecutionMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * TODO
 *
 * @author Dominic Steinhöfel
 */
public class SymbExInterface {
    private KeYEnvironment<DefaultUserInterfaceControl> env;
    private File file;
    private static final Logger logger = LogManager.getFormatterLogger();

    public SymbExInterface(File file) throws ProblemLoaderException {
        this.file = file;
        initializeKeYEnv();
    }

    /**
     * TODO
     * 
     * @throws ProblemLoaderException
     */
    private void initializeKeYEnv() throws ProblemLoaderException {
        logger.trace("Building KeY environment for file %s", file);
        // @formatter:off
        env = KeYEnvironment.load(
//                JavaProfile.getDefaultInstance(),
                SymbolicExecutionJavaProfile.getDefaultInstance(),
                file,     // location
                null,     // class path
                null,     // boot class path
                null,     // includes
                true);    // forceNewProfileOfNewProofs
        // @formatter:on
        logger.trace("Built up environment.");
    }

    /**
     * TODO
     * 
     * @see InformationExtraction#getDeclaredTypes(KeYEnvironment)
     * @return
     */
    public List<KeYJavaType> getDeclaredTypes() {
        return InformationExtraction.getDeclaredTypes(env);
    }

    /**
     * TODO
     * 
     * @param pm
     * @return
     */
    public Goal runUntilLoop(ProgramMethod pm) {
        final ImmutableSet<Contract> contracts = env
                .getSpecificationRepository()
                .getContracts(pm.getContainerType(), pm);

        if (contracts == null || contracts.size() != 1) {
            final String msg = Utilities.format(
                    "Expected 1 contract for method %s, found %s",
                    pm.getFullName(), contracts == null ? 0 : contracts.size());

            logger.error(msg);
            throw new RuntimeException(msg);
        }

        final Contract contract = contracts.iterator().next();

        Proof proof = null;
        try {
            proof = env.createProof(contract.createProofObl( //
                    env.getInitConfig(), contract, true));
            setupStrategy(proof);

            // Start auto mode
            env.getUi().getProofControl().startAndWaitForAutoMode(proof);

            List<Goal> whileLoopGoals = Utilities.toStream(proof.openGoals())
                    .filter(g -> Utilities
                            .toStream(g.node().sequent().succedent())
                            .filter(f -> SymbolicExecutionUtil
                                    .hasSymbolicExecutionLabel(f.formula()))
                            .filter(f -> JavaTools.getActiveStatement(
                                    TermBuilder.goBelowUpdates(f.formula())
                                            .javaBlock()) instanceof While)
                            .findAny().isPresent())
                    .collect(Collectors.toList());

            if (whileLoopGoals.size() != 1) {
                Utilities.logErrorAndThrowRTE(logger,
                        "Expected exactly 1 goal with a while loop, got %s",
                        whileLoopGoals.size());
            }

            return whileLoopGoals.get(0);

        } catch (ProofInputException e) {
            Utilities.logErrorAndThrowRTE(logger,
                    "Exception at '%s' of %s:\n%s", contract.getDisplayName(),
                    contract.getTarget(), e.getMessage());

            return null;
        }

    }

    /**
     * TODO
     * 
     * @param node
     */
    public void finishSEForNode(Node node) {
        List<Node> openNodesWithModality;
        while (!(openNodesWithModality = Utilities
                .toStream(node.proof().getSubtreeGoals(node)).map(g -> g.node())
                .filter(n -> Utilities.toStream(n.sequent().succedent())
                        .anyMatch(
                                f -> f.formula().containsJavaBlockRecursive()))
                .collect(Collectors.toList())).isEmpty()) {
            openNodesWithModality.forEach(
                    n -> applyMacro(new FinishSymbolicExecutionMacro(), n));
        }
        ;
    }

    /**
     * TODO
     * 
     * @param macro
     * @param node
     */
    public void applyMacro(AbstractProofMacro macro, Node node) {
        try {
            macro.applyTo(env.getUi(), node, null, env.getUi());
        } catch (Exception e) {
            Utilities.logErrorAndThrowRTE(logger,
                    "Problem in applying macro, message: %s", e.getMessage());
        }
    }

    /**
     * TODO
     * 
     * @param proof
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
        proof.setActiveStrategy(proof.getServices().getProfile()
                .getDefaultStrategyFactory().create(proof, sp));
    }

    /**
     * TODO
     * 
     * @param proof
     * @return
     */
    private static StrategyProperties strategyProperties(Proof proof) {
        final StrategyProperties sp;
        sp = proof.getSettings().getStrategySettings()
                .getActiveStrategyProperties();

        // @formatter:off
        sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_CONTRACT);
        sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY, StrategyProperties.DEP_ON);
        sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY, StrategyProperties.QUERY_ON);
        sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_DEF_OPS);
        sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY, StrategyProperties.STOPMODE_NONCLOSE);
        sp.setProperty(StrategyProperties.LOOP_OPTIONS_KEY, StrategyProperties.LOOP_NONE);
        sp.setProperty(StrategyProperties.OSS_OPTIONS_KEY, StrategyProperties.OSS_ON);
        // @formatter:on

        proof.getSettings().getStrategySettings()
                .setActiveStrategyProperties(sp);

        return sp;
    }
}
