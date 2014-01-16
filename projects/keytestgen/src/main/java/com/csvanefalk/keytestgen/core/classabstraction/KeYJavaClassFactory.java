package com.csvanefalk.keytestgen.core.classabstraction;

import com.csvanefalk.keytestgen.core.keyinterface.KeYInterface;
import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.core.oracle.OracleGeneratorException;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

/**
 * Produces instances of {@link KeYJavaClass}.
 *
 * @author christopher
 */
public class KeYJavaClassFactory {

    private static KeYJavaClassFactory instance = null;

    public static KeYJavaClassFactory getInstance() {
        if (KeYJavaClassFactory.instance == null) {
            KeYJavaClassFactory.instance = new KeYJavaClassFactory();
        }
        return KeYJavaClassFactory.instance;
    }

    /**
     * Interface to the KeY runtime.
     */
    private final KeYInterface keyInterface = KeYInterface.getInstance();

    private KeYJavaClassFactory() {

    }

    private KeYJavaClass constructClass(final KeYJavaType parent,
                                        final KeYEnvironment<CustomConsoleUserInterface> environment) {

        final Services services = environment.getServices();
        final JavaInfo javaInfo = services.getJavaInfo();

        final KeYJavaClass keYJavaClass = new KeYJavaClass(parent, environment);

        for (final IProgramMethod memberMethod : javaInfo.getAllProgramMethods(parent)) {
            if (!memberMethod.getFullName().startsWith("<")) {

                /*
                 * Extract the operational contracts of the method, and create a
                 * separate abstraction of the method for each one of them
                 * (since each one will effectively represent a unique set of
                 * restrictions on the invocation of the method).
                 */
                final List<FunctionalOperationContract> contracts = getContracts(memberMethod, services);

                /*
                 * If the user has not specified a postcondition, simply let it
                 * be null and delegate to the Oracle Generator.
                 */
                if (contracts.isEmpty()) {

                    final KeYJavaMethod keYJavaMethod = new KeYJavaMethod(keYJavaClass,
                                                                          memberMethod,
                                                                          environment,
                                                                          null);

                    keYJavaClass.addMethodMapping(memberMethod.getFullName(), keYJavaMethod);

                } else {

                    for (final FunctionalOperationContract contract : contracts) {

                        final KeYJavaMethod keYJavaMethod = new KeYJavaMethod(keYJavaClass,
                                                                              memberMethod,
                                                                              environment,
                                                                              contract);

                        keYJavaClass.addMethodMapping(memberMethod.getFullName(), keYJavaMethod);
                    }
                }
            }
        }
        return keYJavaClass;
    }

    /**
     * Manufactures an instance of {@link KeYJavaClass}.
     *
     * @param javaFile path to the corresponding .java file on the local file system
     * @return the {@link KeYJavaClass} instance
     * @throws IOException           if the file could not be found or read
     * @throws KeYInterfaceException
     */
    public KeYJavaClass createKeYJavaClass(final File javaFile) throws IOException, KeYInterfaceException {

        /*
         * Load the file into KeY and get the InitConfig instance for it.
         */
        final KeYEnvironment<CustomConsoleUserInterface> environment = keyInterface.loadJavaFile(javaFile);
        final JavaInfo javaInfo = environment.getServices().getJavaInfo();

        /*
         * Retrieve the KeYJavaType for the top level class declaration in this
         * file
         */

        final String fileName = getFileName(javaFile);
        final String packageName = getPackage(javaFile);
        final String qualifiedName = JavaUtil.isTrimmedEmpty(packageName) ? fileName : packageName + "." + fileName;
        final KeYJavaType mainClass = javaInfo.getKeYJavaType(qualifiedName);

        if (mainClass == null) {
            throw new KeYInterfaceException("Failed to retrieve type information for " + javaFile.getName());
        }

        return constructClass(mainClass, environment);
    }

    public KeYJavaClass createKeYJavaClass(final IExecutionMethodCall methodCall) {

        methodCall.getMediator().getSelectedProof().env().getInitConfig();

        /*
         * Get and process the method call node
         */
        final IProgramMethod method = methodCall.getProgramMethod();

        method.getContainerType();

        return null; // constructClass(parent, initConfig);
    }

    /**
     * Extracts the {@link FunctionalOperationContract} instances for a specific
     * method. Such contracts represent the concrete specifications for the
     * method, i.e. a mapping between a precondition (initial heapstate) and
     * postcondition (postcondition).
     *
     * @param method   the symbolic execution node corresponding to the method call
     * @param services KeY service class
     * @return the contract for the method
     * @throws OracleGeneratorException failure to find a contract for the method is always
     *                                  exceptional
     */
    private List<FunctionalOperationContract> getContracts(final IProgramMethod method, final Services services) {

        final SpecificationRepository specificationRepository = services.getSpecificationRepository();

        /*
         * Extract the abstract representation of the method itself, as well as
         * the type of the class which contains it. Use this information in
         * order to retrieve the specification contracts which exist for the
         * method.
         */
        final KeYJavaType containerClass = method.getContainerType();
        final List<FunctionalOperationContract> contracts = new LinkedList<FunctionalOperationContract>();
        for (final FunctionalOperationContract contract : specificationRepository.getOperationContracts(containerClass,
                                                                                                        method)) {
            contracts.add(contract);
        }
        return contracts;
    }


    /**
     * Strips the file extension from a file name
     *
     * @param file the file to process
     * @return the name of the file
     */
    private String getFileName(final File file) {
        final String name = file.getName();
        final int delimiter = name.indexOf('.');
        return name.substring(0, delimiter);
    }

    /**
     * @param javaFile a valid java source
     * @return the package of the source
     */
    private String getPackage(final File javaFile) throws IOException {
        BufferedReader reader = new BufferedReader(new FileReader(javaFile));
        String next = "";
        while ((next = reader.readLine()) != null) {
            next = next.trim();
            if (next.startsWith("package")) {
                String[] partition = next.split(" ");
                String packageName = partition[partition.length - 1];
                return packageName.substring(0, packageName.indexOf(";"));
            }
        }
        return next;
    }

    public static void __DEBUG_DISPOSE() {
        instance = null;
        KeYInterface.__DEBUG_DISPOSE();
    }
}
