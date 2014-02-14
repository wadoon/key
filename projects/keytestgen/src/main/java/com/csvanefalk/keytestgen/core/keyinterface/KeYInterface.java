package com.csvanefalk.keytestgen.core.keyinterface;

import com.csvanefalk.keytestgen.core.classabstraction.KeYJavaMethod;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStart;
import de.uka.ilkd.key.symbolic_execution.po.ProgramMethodPO;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.util.IFilter;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

import java.io.File;
import java.io.IOException;
import java.util.Map;
import java.util.concurrent.locks.ReentrantLock;

/**
 * This singleton provides services on behalf of a single KeY runtime instance
 * to the rest of KeYTestGen. No part of KeYTestGen apart from this class should
 * ever be allowed to in any way manipulate the KeY internals, or otherwise
 * interact directly with the KeY runtime.
 * <p/>
 * Use of this singleton is synchronized in order to make sure that no thread is
 * able to request services of the KeY runtime until another one has completely
 * finished doing so, due to concerns about the thread safety of KeY itself.
 *
 * @author christopher
 */
public class KeYInterface {

    private static KeYInterface instance = null;


    /*
     *Set stop condition to stop after a number of detected symbolic execution tree nodes instead of applied rules
     */
    private static final int maximalNumberOfExecutedSetNodes = ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN;

    /**
     * Used to ensure atomic access to KeY services.
     */
    private static final ReentrantLock lock = new ReentrantLock(true);

    /**
     * Assert that a given object is not null, and raise an exception if it
     * is.
     *
     * @param object         the object to check
     * @param failureMessage message to pass in the event that the object is null
     * @throws KeYInterfaceException the generated exception if the object is null
     */
    private static void assertNotNull(final Object object, final String failureMessage) throws KeYInterfaceException {

        if (object == null) {
            throw new KeYInterfaceException(failureMessage);
        }
    }

    // DEBUG - disposes of the interface
    public static void __DEBUG_DISPOSE() {
        instance = null;
    }

    /**
     * @return the KeYInterface singleton.
     */
    public static KeYInterface getInstance() {
        if (KeYInterface.instance == null) {
            KeYInterface.instance = new KeYInterface();
        }
        return KeYInterface.instance;
    }

    private KeYInterface() {
    }

    /**
     * Create a {@link Proof} for a given method.
     *
     * @param environment
     * @param method       the method to generate the proof for
     * @param precondition an optional precondition for the method
     * @return the proof
     * @throws ProofInputException in the event that the proof cannot be created
     */
    private Proof getProof(final KeYEnvironment<CustomConsoleUserInterface> environment,
                           final IProgramMethod method,
                           final String precondition) throws ProofInputException {

        final ProofOblInput proofObligationInput = new ProgramMethodPO(environment.getInitConfig(),
                                                                       method.getFullName(),
                                                                       method,
                                                                       precondition,
                                                                       true,
                                                                       true);

        final Proof proof = environment.createProof(proofObligationInput);

        if (proof == null) {
            throw new ProofInputException("Unable to load proof");
        }

        /*
         * Setup a strategy and goal chooser for the proof session
         */
        //SymbolicExecutionUtil.configureProof(proof);
        SymbolicExecutionEnvironment.configureProofForSymbolicExecution(proof,
                                                                        ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN,
                                                                        false,
                                                                        false,
                                                                        false,
                                                                        false);

        return proof;
    }

    /**
     * Symbolically execute a given method, and return the resulting symbolic
     * execution tree.
     * <p/>
     * Uses code by Martin Hentschel.
     *
     * @param method the method
     * @return the symbolic execution tree
     * @throws KeYInterfaceException in the event that a symbolic execution tree cannot be
     *                               generated.
     */
    public IExecutionStart getSymbolicExecutionTree(final KeYJavaMethod method) throws KeYInterfaceException {

        try {

            KeYInterface.lock.lock();

            //Prettyprinting can be left on for debugging. Probably not appropriate for production environments.
            SymbolicExecutionEnvironment<CustomConsoleUserInterface> env = createSymbolicExecutionEnvironment(method,
                                                                                                              false,
                                                                                                             true,
                                                                                                              true,
                                                                                                              false,
                                                                                                              false);

            ExecutedSymbolicExecutionTreeNodesStopCondition stopCondition = new ExecutedSymbolicExecutionTreeNodesStopCondition(
                    maximalNumberOfExecutedSetNodes);

            env.getProof().getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(stopCondition);
            int nodeCount;
            // Execute auto mode until no more symbolic execution tree nodes are found or no new rules are applied.
            do {
                // Store the number of nodes before start of the auto mode
                nodeCount = env.getProof().countNodes();
                // Run proof
                env.getUi().startAndWaitForAutoMode(env.getProof());
                // Update symbolic execution tree
                env.getBuilder().analyse();
                // Make sure that not to many set nodes are executed
                Map<Goal, Integer> executedSetNodesPerGoal = stopCondition.getExectuedSetNodesPerGoal();
                for (Integer value : executedSetNodesPerGoal.values()) {
                    assert (value != null);
                    assert (value.intValue() <= maximalNumberOfExecutedSetNodes);
                }
            } while (stopCondition.wasSetNodeExecuted() && nodeCount != env.getProof().countNodes());

            return env.getBuilder().getStartNode();

        } catch (final ProofInputException e) {

            throw new KeYInterfaceException("FATAL: could not create proof: " + e.getMessage());

        } finally {
            KeYInterface.lock.unlock();
        }
    }

    /**
     * Load a given file into the KeY system, and return the {@link InitConfig}
     * instance for it.
     *
     * @param javaFile the file to load
     * @return the {@link InitConfig} instance for the file
     * @throws KeYInterfaceException
     * @throws ProofInputException   in case the proof could not be initiated
     * @throws IOException           in case the File could not be found, or is not accessible
     */
    public KeYEnvironment<CustomConsoleUserInterface> loadJavaFile(final File javaFile) throws KeYInterfaceException {

        try {

            KeYInterface.lock.lock();

            /*
             * Manually load the classpath needed to symbolically execute this file.
             */
            /*
            List<File> classpath = new ArrayList<File>();
            for (String path : System.getProperty("java.class.path").split(":")) {
                System.out.println(path);
                classpath.add(new File(path));
            }
            */
            return KeYEnvironment.load(SymbolicExecutionJavaProfile.getDefaultInstance(), javaFile, null, null);

        } catch (final ProblemLoaderException e) {
            throw new KeYInterfaceException(e.getMessage(), e);
        } finally {
            KeYInterface.lock.unlock();
        }
    }

    /**
     * Original code by Martin Hentschel.
     * <p/>
     * Creates a {@link SymbolicExecutionEnvironment} which consists
     * of loading a file to load, finding the method to proof, instantiation
     * of proof and creation with configuration of {@link SymbolicExecutionTreeBuilder}.
     *
     * @param mergeBranchConditions              Merge branch conditions?
     * @param useOperationContracts              Use operation contracts?
     * @param useLoopInvarints                   Use loop invariants?
     * @param nonExecutionBranchHidingSideProofs {@code true} hide non execution branch labels by side proofs, {@code false} do not hide execution branch labels.
     * @param aliasChecks                        Do alias checks?
     * @return The created {@link SymbolicExecutionEnvironment}.
     * @throws ProblemLoaderException Occurred Exception.
     * @throws ProofInputException    Occurred Exception.
     */
    private SymbolicExecutionEnvironment<CustomConsoleUserInterface> createSymbolicExecutionEnvironment(KeYJavaMethod method,
                                                                                                        boolean mergeBranchConditions,
                                                                                                        boolean useOperationContracts,
                                                                                                        boolean useLoopInvarints,
                                                                                                        boolean nonExecutionBranchHidingSideProofs,
                                                                                                        boolean aliasChecks) throws ProblemLoaderException, ProofInputException {

        KeYEnvironment<CustomConsoleUserInterface> environment = method.getEnvironment();

        /*IProgramMethod pm = method.getProgramMethod();
        ImmutableSet<Contract> contracts = environment.getServices().getSpecificationRepository().getContracts(pm.getContainerType(), pm);
        Contract contract = contracts.iterator().next(); // TODO; In case of also you have multiple contracts. Select the one you need
        ProofOblInput input = contract.createProofObl(environment.getInitConfig(), contract);*/
        
        // Start proof
        ProofOblInput input = new ProgramMethodPO(environment.getInitConfig(),
                                                  method.getProgramMethod().getFullName(),
                                                  method.getProgramMethod(),
                                                  null,
                                                  true,
                                                  true);
        //ProofOblInput input = new FunctionalOperationContractPO(method.getInitConfig(), method.getFunctionalContract());
        Proof proof = environment.createProof(input);
        assert (proof != null);

        // Set strategy and goal chooser to use for auto mode
        SymbolicExecutionEnvironment.configureProofForSymbolicExecution(proof,
                                                                        maximalNumberOfExecutedSetNodes,
                                                                        useOperationContracts,
                                                                        useLoopInvarints,
                                                                        nonExecutionBranchHidingSideProofs,
                                                                        aliasChecks);

        // Create symbolic execution tree which contains only the start node at beginning
        SymbolicExecutionTreeBuilder builder = new SymbolicExecutionTreeBuilder(environment.getMediator(),
                                                                                proof,
                                                                                mergeBranchConditions,
                                                                                false);
        //builder.analyse();
        //assert (builder.getStartNode() != null);
        return new SymbolicExecutionEnvironment<CustomConsoleUserInterface>(environment, builder);
    }

    /**
     * Original code by Martin Hentschel.
     * <p/>
     * Searches a {@link IProgramMethod} in the given {@link Services}.
     *
     * @param services          The {@link Services} to search in.
     * @param containerTypeName The name of the type which contains the method.
     * @param methodFullName    The method name to search.
     * @return The first found {@link IProgramMethod} in the type.
     */
    private IProgramMethod searchProgramMethod(Services services,
                                               String containerTypeName,
                                               final String methodFullName) {

        JavaInfo javaInfo = services.getJavaInfo();
        KeYJavaType containerKJT = javaInfo.getTypeByClassName(containerTypeName);
        ImmutableList<IProgramMethod> pms = javaInfo.getAllProgramMethods(containerKJT);
        IProgramMethod pm = JavaUtil.search(pms, new IFilter<IProgramMethod>() {
            @Override
            public boolean select(IProgramMethod element) {
                return methodFullName.equals(element.getFullName());
            }
        });
        if (pm == null) {
            pms = javaInfo.getConstructors(containerKJT);
            pm = JavaUtil.search(pms, new IFilter<IProgramMethod>() {
                @Override
                public boolean select(IProgramMethod element) {
                    return methodFullName.equals(element.getFullName());
                }
            });
        }
        assert (pm != null);
        return pm;
    }
}