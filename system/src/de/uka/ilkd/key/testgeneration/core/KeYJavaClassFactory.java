package de.uka.ilkd.key.testgeneration.core;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.PackageReference;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.ContractWrapper;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContractImpl;
import de.uka.ilkd.key.testgeneration.core.keyinterface.KeYInterface;
import de.uka.ilkd.key.testgeneration.core.keyinterface.KeYInterfaceException;
import de.uka.ilkd.key.testgeneration.core.oraclegeneration.OracleGeneratorException;
import de.uka.ilkd.key.testgeneration.core.parsers.JavaSourceParser;

/**
 * Produces instances of {@link KeYJavaClass}.
 * 
 * @author christopher
 */
public enum KeYJavaClassFactory {
    INSTANCE;

    /**
     * Interface to the KeY runtime.
     */
    private final KeYInterface keyInterface = KeYInterface.INSTANCE;

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
    public KeYJavaClass createKeYJavaClass(File javaFile) throws IOException,
            KeYInterfaceException {

        /*
         * Load the file into KeY and get the InitConfig instance for it.
         */
        InitConfig initConfig = keyInterface.loadJavaFile(javaFile);

        Services services = initConfig.getServices();
        JavaInfo javaInfo = initConfig.getServices().getJavaInfo();

        /*
         * Retrieve the KeYJavaType for the top level class declaration in this
         * file
         */
        String fileName = getFileName(javaFile);
        KeYJavaType mainClass = javaInfo.getKeYJavaType(fileName);

        /*
         * Setup the class
         */
        KeYJavaClass javaClass = new KeYJavaClass(mainClass);

        /*
         * Extract all methods declared in this class (including the ones
         * provided in Java.lang.Object, even if these have not been
         * overridden), and create name-value mappings for them. Exclude
         * implicit methods (i.e. <create>, <init> etc).
         */
        for (IProgramMethod method : javaInfo.getAllProgramMethods(mainClass)) {
            if (!method.getFullName().startsWith("<")) {

                /*
                 * Extract the operational contracts of the method, and create a
                 * separate abstraction of the method for each one of them
                 * (since each one will effectively represent a unique set of
                 * restrictions on the invocation of the method).
                 */
                List<ContractWrapper> contracts = getContracts(method, services);
                for (ContractWrapper contract : contracts) {

                    KeYJavaMethod keYJavaMethod = new KeYJavaMethod(javaClass,
                            method, initConfig, contract);

                    javaClass.addMethodMapping(method.getFullName(),
                            keYJavaMethod);
                }
            }
        }

        return javaClass;
    }
    
    public KeYJavaClass createKeYJavaClass(KeYJavaType classType, Services services) {
        
        
        
        return null;
    }

    /**
     * Strips the file extension from a file name
     * 
     * @param file
     *            the file to process
     * @return the name of the file
     */
    private String getFileName(File file) {

        String name = file.getName();
        int delimiter = name.indexOf('.');
        return name.substring(0, delimiter);
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
    private List<ContractWrapper> getContracts(IProgramMethod method,
            Services services) {

        SpecificationRepository specificationRepository = services
                .getSpecificationRepository();

        /*
         * Extract the abstract representation of the method itself, as well as
         * the type of the class which contains it. Use this information in
         * order to retrieve the specification contracts which exist for the
         * method.
         */
        KeYJavaType containerClass = method.getContainerType();
        List<ContractWrapper> contracts = new LinkedList<ContractWrapper>();
        for (FunctionalOperationContract contract : specificationRepository
                .getOperationContracts(containerClass, method)) {
            contracts.add(new ContractWrapper(
                    (FunctionalOperationContractImpl) contract));
        }

        return contracts;
    }
}
