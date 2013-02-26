package de.uka.ilkd.key.testgeneration.core.keyinterface;

import java.io.File;
import java.io.IOException;
import java.util.concurrent.locks.ReentrantLock;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.DefaultProblemLoader;
import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.symbolic_execution.po.ProgramMethodPO;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.testgeneration.core.KeYJavaMethod;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * This singleton provides services on behalf of a single KeY runtime instance
 * to the rest of KeYTestGen. No part of KeYTestGen apart from this class should
 * ever be allowed to in any way manipulate the KeY internals, or otherwise
 * interact directly with the KeY runtime.
 * <p>
 * Use of this singleton is synchronized in order to make sure that no thread is
 * able to request services of the KeY runtime until another one has completely
 * finished doing so, due to concerns about the thread safety of KeY itself.
 * 
 * @author christopher
 */
public enum KeYInterface {
    INSTANCE;

    /**
     * Main interface to the KeY system itself.
     */
    private CustomConsoleUserInterface userInterface = new CustomConsoleUserInterface(
            false);

    /**
     * The public methods of this singleton must use this {@link ReentrantLock}
     * instance in order to guarantee atomic access to the singleton at all
     * times. Private methods need not use the lock. Further, no two public
     * methods using the lock are allowed to call each other under any
     * circumstances, in order to make sure that a single thread no longer
     * requires services from KeY before another requests them.
     */
    private static final ReentrantLock lock = new ReentrantLock(true);

    /**
     * Load a given file into the KeY system, and return the {@link InitConfig}
     * instance for it.
     * 
     * @param javaFile
     *            the file to load
     * @return the {@link InitConfig} instance for the file
     * @throws KeYInterfaceException
     * @throws ProofInputException
     *             in case the proof could not be initiated
     * @throws IOException
     *             in case the File could not be found, or is not accessible
     */
    public InitConfig loadJavaFile(File javaFile) throws KeYInterfaceException {

        try {

            lock.lock();

            DefaultProblemLoader loader = userInterface.load(javaFile, null,
                    null);

            InitConfig initConfig = loader.getInitConfig();

            return initConfig;

        } catch (ProblemLoaderException e) {

            throw new KeYInterfaceException(e.getMessage());
        } finally {

            lock.unlock();
        }
    }

    /**
     * Symbolically execute a given method, and return the resulting symbolic
     * execution tree.
     * 
     * @param method
     *            the method
     * @return the symbolic execution tree
     * @throws KeYInterfaceException
     *             in the event that a symbolic execution tree cannot be
     *             generated.
     */
    public IExecutionStartNode getSymbolicExecutionTree(KeYJavaMethod method)
            throws KeYInterfaceException {

        try {

            lock.lock();

            /*
             * Setup and prepare the proof session, and retrieve the KeYMediator
             * instance to use.
             */
            Proof proof = getProof(method.getInitConfig(),
                    method.getProgramMethod(), null);
            KeYMediator mediator = userInterface.getMediator();

            /*
             * Create the symbolic execution tree builder.
             */
            SymbolicExecutionTreeBuilder builder = new SymbolicExecutionTreeBuilder(
                    mediator, proof, false);

            /*
             * Add a stop condition for the proof (we use a default in order to
             * assure maximum coverage of execution paths). Start the proof and
             * wait for it to finish.
             */
            proof.getSettings()
                    .getStrategySettings()
                    .setCustomApplyStrategyStopCondition(
                            new ExecutedSymbolicExecutionTreeNodesStopCondition(
                                    ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN));

            userInterface.startAndWaitForAutoMode(proof);

            /*
             * Create the symbolic execution tree, and assert that it indeed
             * exists.
             */
            builder.analyse();
            IExecutionStartNode rootNode = builder.getStartNode();
            assertNotNull(rootNode, "FATAL: unable to initialize proof tree");

            return builder.getStartNode();

        } catch (ProofInputException e) {

            throw new KeYInterfaceException("FATAL: could not create proof: "
                    + e.getMessage());

        } finally {
            lock.unlock();
        }
    }

    /**
     * Assert that a given object is not null, and generate an exception if it
     * is.
     * 
     * @param object
     *            the object to check
     * @param failureMessage
     *            message to pass in the event that the object is null
     * @throws KeYInterfaceException
     *             the generated exception if the object is null
     */
    private static void assertNotNull(Object object, String failureMessage)
            throws KeYInterfaceException {

        if (object == null) {
            throw new KeYInterfaceException(failureMessage);
        }
    }

    /**
     * Create a {@link Proof} for a given method.
     * 
     * @param initConfig
     *            the {@link InitConfig} instance for the Java file which the
     *            method is part of.
     * @param method
     *            the method to generate the proof for
     * @param precondition
     *            an optional precondition for the method
     * @return the proof
     * @throws ProofInputException
     *             in the event that the proof cannot be created
     */
    private Proof getProof(InitConfig initConfig, IProgramMethod method,
            String precondition) throws ProofInputException {

        ProofOblInput proofObligationInput = new ProgramMethodPO(initConfig,
                method.getFullName(), method, precondition, true);

        Proof proof = userInterface.createProof(initConfig,
                proofObligationInput);
        if (proof == null) {
            throw new ProofInputException("Unable to load proof");
        }

        /*
         * Setup a strategy and goal chooser for the proof session
         */
        SymbolicExecutionEnvironment
                .configureProofForSymbolicExecution(
                        proof,
                        ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN,
                        true, true);

        return proof;
    }

    public void __DEBUG_RESET() {
        userInterface = new CustomConsoleUserInterface(false);
    }
}