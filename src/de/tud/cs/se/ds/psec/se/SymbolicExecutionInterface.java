package de.tud.cs.se.ds.psec.se;

import java.io.File;
import java.util.HashMap;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.po.ProgramMethodPO;
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.MiscTools;

/**
 * Bridge to KeY's symbolic execution engine.
 *
 * @author Dominic Scheurer
 * @see SymbolicExecutionTreeBuilder
 */
public class SymbolicExecutionInterface {
    private KeYEnvironment<DefaultUserInterfaceControl> environment;
    private File javaFile;

    /**
     * Constructs a new {@link SymbolicExecutionInterface} for the given
     * {@link KeYEnvironment} and Java {@link File}.
     * 
     * @param environment
     *            The {@link KeYEnvironment} generated for the given
     *            {@link File} comprising the method to execute.
     * @param javaFile
     *            The {@link File} containing the method to execute.
     */
    public SymbolicExecutionInterface(
            KeYEnvironment<DefaultUserInterfaceControl> environment,
            File javaFile) {
        this.environment = environment;
        this.javaFile = javaFile;
    }

    /**
     * Symbolically executes the given {@link ProgramMethod} and returns the
     * created symbolic execution tree, which can be accessed through
     * {@link SymbolicExecutionTreeBuilder#getStartNode()} and
     * {@link SymbolicExecutionTreeBuilder#getProof()}.
     *
     * @param pm
     *            The {@link ProgramMethod} to symbolically execute.
     * @return The generated Symbolic Execution Tree (SET).
     */
    public SymbolicExecutionTreeBuilder execute(ProgramMethod pm) {
        try {
            // Set Taclet options
            ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS
                    .getChoiceSettings();
            HashMap<String, String> oldSettings = choiceSettings
                    .getDefaultChoices();
            HashMap<String, String> newSettings = new HashMap<String, String>(
                    oldSettings);
            newSettings.putAll(MiscTools.getDefaultTacletOptions());
            choiceSettings.setDefaultChoices(newSettings);
            try {
                // Instantiate proof for symbolic execution of the program
                // method (Java semantics)
                //@formatter:off
                AbstractOperationPO po = new ProgramMethodPO(environment.getInitConfig(), 
                                                             "Symbolic Execution of " + pm, 
                                                             pm, 
                                                             null,  // An optional precondition
                                                             true,  // Needs to be true for symbolic execution!
                                                             true); // Needs to be true for symbolic execution!
                //@formatter:on
                Proof proof = environment.createProof(po);

                // Create symbolic execution tree builder
                //@formatter:off
                SymbolicExecutionTreeBuilder builder = new SymbolicExecutionTreeBuilder(proof, 
                                                                                        false, // Merge branch conditions 
                                                                                        false, // Use Unicode? 
                                                                                        true,  // Use Pretty Printing? 
                                                                                        true,  // Variables are collected from updates instead of the visible type structure 
                                                                                        true); // Simplify conditions
                //@formatter:on

                builder.analyse();

                // Optionally, create an SymbolicExecutionEnvironment which
                // provides access to all relevant objects for symbolic
                // execution
                SymbolicExecutionEnvironment<DefaultUserInterfaceControl> symbolicEnv =
                        new SymbolicExecutionEnvironment<DefaultUserInterfaceControl>(
                                environment, builder);

                // Configure strategy for full exploration
                SymbolicExecutionUtil.initializeStrategy(builder);
                //@formatter:off
                SymbolicExecutionEnvironment.configureProofForSymbolicExecution(proof, 
                                                                                100, 
                                                                                true,   // true to apply method contracts instead of inlining, 
                                                                                false,  // true to apply loop invariants instead of unrolling, 
                                                                                false,  // true to apply block contracts instead of expanding.
                                                                                false,  // true to hide branch conditions caused by symbolic execution within modalities not of interest, 
                                                                                false); // true to perform alias checks during symbolic execution
                //@formatter:on

                // Optionally, add a more advanced stop conditions like
                // breakpoints
                CompoundStopCondition stopCondition =
                        new CompoundStopCondition();

                //@formatter:off
                // Stop after 100 nodes have been explored on each branch.
                //TODO: Check whether this stop condition is really practical
                stopCondition.addChildren(new ExecutedSymbolicExecutionTreeNodesStopCondition(500));
                //@formatter:on

                proof.getSettings().getStrategySettings()
                        .setCustomApplyStrategyStopCondition(stopCondition);

                // Perform strategy which will stop at given stop condition
                symbolicEnv.getProofControl().startAndWaitForAutoMode(proof);

                builder.analyse();

                // Perform strategy again to complete symbolic execution tree
                symbolicEnv.getProofControl().startAndWaitForAutoMode(proof);

                builder.analyse();

                return builder;
            } finally {
                environment.dispose(); // Ensure always that all instances of
                                       // KeYEnvironment are disposed
            }
        } catch (Exception e) {
            System.out.println(
                    "Exception at '" + javaFile.getAbsolutePath() + "':");
            e.printStackTrace();
        }

        return null;
    }
}
