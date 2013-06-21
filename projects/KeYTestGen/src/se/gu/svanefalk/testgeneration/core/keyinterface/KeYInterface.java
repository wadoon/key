package se.gu.svanefalk.testgeneration.core.keyinterface;

import java.io.File;
import java.io.IOException;
import java.util.concurrent.locks.ReentrantLock;

import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaMethod;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.symbolic_execution.po.ProgramMethodPO;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
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
public class KeYInterface {

    private static KeYInterface instance = null;

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
    private static void assertNotNull(final Object object,
            final String failureMessage) throws KeYInterfaceException {

        if (object == null) {
            throw new KeYInterfaceException(failureMessage);
        }
    }

    public static KeYInterface getInstance() {
        if (KeYInterface.instance == null) {
            KeYInterface.instance = new KeYInterface();
        }
        return KeYInterface.instance;
    }

    private final CustomConsoleUserInterface keyInterface = new CustomConsoleUserInterface(
            false);

    private KeYInterface() {
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
    private Proof getProof(
            final KeYEnvironment<CustomConsoleUserInterface> environment,
            final IProgramMethod method, final String precondition)
            throws ProofInputException {

        final ProofOblInput proofObligationInput = new ProgramMethodPO(
                environment.getInitConfig(), method.getFullName(), method,
                precondition, true, true);

        final Proof proof = environment.createProof(proofObligationInput);

        if (proof == null) {
            throw new ProofInputException("Unable to load proof");
        }

        /*
         * Setup a strategy and goal chooser for the proof session
         */
        SymbolicExecutionUtil.configureProof(proof);
        SymbolicExecutionEnvironment.configureProofForSymbolicExecution(
                proof,
                ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN,
                false, false, false);

        return proof;
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
    public IExecutionStartNode getSymbolicExecutionTree(
            final KeYJavaMethod method) throws KeYInterfaceException {

        try {

            KeYInterface.lock.lock();

            /*
             * Setup and prepare the proof session, and retrieve the KeYMediator
             * instance to use.
             */
            final Proof proof = getProof(method.getEnvironment(),
                    method.getProgramMethod(), null);
            final KeYMediator mediator = method.getEnvironment().getMediator();

            /*
             * Create the symbolic execution tree builder, and associate it with
             * an environment.
             */
            final SymbolicExecutionTreeBuilder builder = new SymbolicExecutionTreeBuilder(
                    mediator, proof, false);

            final SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment = new SymbolicExecutionEnvironment<>(
                    method.getEnvironment(), builder);

            /*
             * Setup the stop condition for the symbolic execution process.
             */
            final ExecutedSymbolicExecutionTreeNodesStopCondition stopCondition = new ExecutedSymbolicExecutionTreeNodesStopCondition(
                    ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN);
            environment.getProof().getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(
                    stopCondition);
            // SymbolicExecutionUtil.updateStrategyPropertiesForSymbolicExecution(environment.getProof());

            /*
             * Symbolically execute the code, and extract the root of the
             * resulting symbolic execution tree.
             */
            environment.getUi().startAndWaitForAutoMode(environment.getProof());
            environment.getBuilder().analyse();

            final IExecutionStartNode rootNode = builder.getStartNode();
            KeYInterface.assertNotNull(rootNode,
                    "FATAL: unable to initialize proof tree");

            return rootNode;

        } catch (final ProofInputException e) {

            throw new KeYInterfaceException("FATAL: could not create proof: "
                    + e.getMessage());

        } finally {
            KeYInterface.lock.unlock();
        }
    }

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
    public KeYEnvironment<CustomConsoleUserInterface> loadJavaFile(
            final File javaFile) throws KeYInterfaceException {

        try {

            KeYInterface.lock.lock();

            final KeYEnvironment<CustomConsoleUserInterface> environment = KeYEnvironment.load(
                    javaFile, null, null);

            return environment;

        } catch (final ProblemLoaderException e) {

            throw new KeYInterfaceException(e.getMessage());
        } finally {

            KeYInterface.lock.unlock();
        }
    }
}