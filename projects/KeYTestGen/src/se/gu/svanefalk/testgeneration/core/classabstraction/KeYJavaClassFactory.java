package se.gu.svanefalk.testgeneration.core.classabstraction;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterface;
import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import se.gu.svanefalk.testgeneration.core.model.implementation.ModelGenerator;
import se.gu.svanefalk.testgeneration.core.oracle.OracleGeneratorException;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.ContractWrapper;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContractImpl;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;

/**
 * Produces instances of {@link KeYJavaClass}.
 * 
 * @author christopher
 */
public class KeYJavaClassFactory {
    
    private static KeYJavaClassFactory instance = null;

    public static KeYJavaClassFactory getInstance() {
        if (instance == null) {
            instance = new KeYJavaClassFactory();
        }
        return instance;
    }
    
    private KeYJavaClassFactory() {
        
    }

    /**
     * Interface to the KeY runtime.
     */
    private final KeYInterface keyInterface = KeYInterface.getInstance();

    private KeYJavaClass constructClass(final KeYJavaType parent,
            final InitConfig initConfig) {

        final Services services = initConfig.getServices();
        final JavaInfo javaInfo = services.getJavaInfo();

        final KeYJavaClass keYJavaClass = new KeYJavaClass(parent);

        for (final IProgramMethod memberMethod : javaInfo.getAllProgramMethods(parent)) {
            if (!memberMethod.getFullName().startsWith("<")) {

                /*
                 * Extract the operational contracts of the method, and create a
                 * separate abstraction of the method for each one of them
                 * (since each one will effectively represent a unique set of
                 * restrictions on the invocation of the method).
                 */
                final List<ContractWrapper> contracts = getContracts(
                        memberMethod, services);
                for (final ContractWrapper contract : contracts) {

                    final KeYJavaMethod keYJavaMethod = new KeYJavaMethod(
                            keYJavaClass, memberMethod, initConfig, contract);

                    keYJavaClass.addMethodMapping(memberMethod.getFullName(),
                            keYJavaMethod);
                }
            }
        }
        return keYJavaClass;
    }

    /**
     * Manufactures an instance of {@link KeYJavaClass}.
     * 
     * @param absolutePath
     *            path to the corresponding .java file on the local file system
     * @return the {@link KeYJavaClass} instance
     * @throws IOException
     *             if the file could not be found or read
     * @throws KeYInterfaceException
     */
    public KeYJavaClass createKeYJavaClass(final File javaFile)
            throws IOException, KeYInterfaceException {

        /*
         * Load the file into KeY and get the InitConfig instance for it.
         */
        final InitConfig initConfig = keyInterface.loadJavaFile(javaFile);
        final JavaInfo javaInfo = initConfig.getServices().getJavaInfo();

        /*
         * Retrieve the KeYJavaType for the top level class declaration in this
         * file
         */
        final String fileName = getFileName(javaFile);
        final KeYJavaType mainClass = javaInfo.getKeYJavaType(fileName);

        return constructClass(mainClass, initConfig);
    }

    public KeYJavaClass createKeYJavaClass(final IExecutionMethodCall methodCall) {

        final InitConfig initConfig = methodCall.getMediator().getProof().env().getInitConfig();

        /*
         * Get and process the method call node
         */
        final IProgramMethod method = methodCall.getProgramMethod();

        /*
         * Construct the KeYJavaClass itself
         */
        final KeYJavaType parent = method.getContainerType();

        return constructClass(parent, initConfig);
    }

    /**
     * Extracts the {@link FunctionalOperationContract} instances for a specific
     * method. Such contracts represent the concrete specifications for the
     * method, i.e. a mapping between a precondition (initial heapstate) and
     * postcondition (postcondition).
     * 
     * @param methodCallNode
     *            the symbolic execution node corresponding to the method call
     * @return the contract for the method
     * @throws OracleGeneratorException
     *             failure to find a contract for the method is always
     *             exceptional
     */
    private List<ContractWrapper> getContracts(final IProgramMethod method,
            final Services services) {

        final SpecificationRepository specificationRepository = services.getSpecificationRepository();

        /*
         * Extract the abstract representation of the method itself, as well as
         * the type of the class which contains it. Use this information in
         * order to retrieve the specification contracts which exist for the
         * method.
         */
        final KeYJavaType containerClass = method.getContainerType();
        final List<ContractWrapper> contracts = new LinkedList<ContractWrapper>();
        for (final FunctionalOperationContract contract : specificationRepository.getOperationContracts(
                containerClass, method)) {
            contracts.add(new ContractWrapper(
                    (FunctionalOperationContractImpl) contract));
        }

        return contracts;
    }

    /**
     * Strips the file extension from a file name
     * 
     * @param file
     *            the file to process
     * @return the name of the file
     */
    private String getFileName(final File file) {

        final String name = file.getName();
        final int delimiter = name.indexOf('.');
        return name.substring(0, delimiter);
    }

}
