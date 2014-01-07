package com.csvanefalk.keytestgen.testutils;

import com.csvanefalk.keytestgen.core.classabstraction.KeYJavaClass;
import com.csvanefalk.keytestgen.core.classabstraction.KeYJavaClassFactory;
import com.csvanefalk.keytestgen.core.classabstraction.KeYJavaMethod;
import com.csvanefalk.keytestgen.core.keyinterface.KeYInterface;
import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStart;
import org.junit.Assert;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class TestEnvironment {

    /**
     * Interface to KeY itself
     */
    private final static KeYInterface keYInterface = KeYInterface.getInstance();

    /**
     * Repository of loaded folders.
     */
    private static final Map<String, TestEnvironment> repository = new HashMap<String, TestEnvironment>();

    private TestEnvironment() {
        symbolicTrees = new HashMap<String, IExecutionStart>();
    }

    public static synchronized TestEnvironment loadEnvironmentForDirectory(String directory,
                                                                           boolean includeSubdirectories,
                                                                           String... files) throws KeYInterfaceException, IOException {

        if (repository.containsKey(directory)) {
            return repository.get(directory);
        }

        /*
         * Get the corresponding KeyJavaClass instances for each sourcefile in
         * the target directory.
         */
        FileEnvironment fileEnvironment = FileEnvironment.constructFileEnvironment(directory, includeSubdirectories, files);

        List<KeYJavaClass> keYJavaClasses = loadKeYJavaFiles(fileEnvironment.getFiles());

        /*
         * Symbolically execute all methods, and prepare the mapping.
         */
        Map<String, IExecutionStart> trees = new HashMap<String, IExecutionStart>();
        for (KeYJavaClass keYJavaClass : keYJavaClasses) {

            for (String methoIdentifier : keYJavaClass.getMethods()) {

                KeYJavaMethod method = keYJavaClass.getMethod(methoIdentifier);

                if (!isNativeMethod(method)) {

                    IExecutionStart tree = keYInterface.getSymbolicExecutionTree(method);
                    Assert.assertNotNull(tree);

                    String fullMethodName = method.getDeclaringClass().getName() + "." + methoIdentifier;
                    trees.put(fullMethodName, tree);
                }
            }
        }
        TestEnvironment testEnvironment = new TestEnvironment(trees);
        repository.put(directory, testEnvironment);
        return testEnvironment;
    }

    /**
     * Symbolic trees for the methods mapped by this environment.
     */
    private final Map<String, IExecutionStart> symbolicTrees;

    private TestEnvironment(Map<String, IExecutionStart> trees) {
        this.symbolicTrees = trees;
    }

    /**
     * Getsthe symbolic execution tree for a given method.
     *
     * @param identifier
     * @return
     */
    public IExecutionStart getSymbolicTreeForNode(String identifier) {
        return symbolicTrees.get(identifier);
    }

    /**
     * Load a set of corresponding {@link KeYJavaClass} instances for a set of
     * legitimate Java files.
     *
     * @param javaFiles the java files
     * @return the KeY abstractions
     * @throws KeYInterfaceException
     * @throws IOException
     */
    protected static List<KeYJavaClass> loadKeYJavaFiles(List<File> javaFiles) throws KeYInterfaceException, IOException {

        List<KeYJavaClass> keYJavaClasses = new LinkedList<KeYJavaClass>();
        KeYJavaClassFactory factory = KeYJavaClassFactory.getInstance();
        for (File javaFile : javaFiles) {
            KeYJavaClass keYJavaClass = factory.createKeYJavaClass(javaFile);
            Assert.assertNotNull(keYJavaClass);
            keYJavaClasses.add(keYJavaClass);
        }

        return keYJavaClasses;
    }

    /**
     * A list of native methods (i.e. those part of any type with {@link Object}
     * as its supertype). We use this list in the event that we wish to ignore
     * such methods while generating test cases.
     */
    private static final LinkedList<String> nativeMethods = new LinkedList<String>();

    static {
        nativeMethods.add("equals");
        nativeMethods.add("toString");
        nativeMethods.add("wait");
        nativeMethods.add("notify");
        nativeMethods.add("notifyAll");
        nativeMethods.add("hashCode");
        nativeMethods.add("clone");
        nativeMethods.add("finalize");
    }

    private static boolean isNativeMethod(KeYJavaMethod method) {

        return nativeMethods.contains(method.getName());
    }
}
