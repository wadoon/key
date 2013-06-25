package se.gu.svanefalk.testgeneration;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.net.URL;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Properties;

import org.junit.Assert;
import org.junit.Test;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;

import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaClass;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaClassFactory;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaMethod;
import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterface;
import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import se.gu.svanefalk.testgeneration.util.transformers.RemoveObserverFunctionsTransformer;

public class TestEnvironment {

    /**
     * Absolute path inside the KeYTestGen root folder to the repository of test
     * models.
     */
    protected final static String targetModelsPath = "test/se/gu/svanefalk/testgeneration/targetmodels/";

    /**
     * Relative OS path to the KeYTestGen folder.
     */
    protected final static String keYTestGenPath = System.getProperty("user.dir")
            + "/";

    /**
     * Interface to KeY itself
     */
    private final static KeYInterface keYInterface = KeYInterface.getInstance();

    /**
     * Repository of loaded folders.
     */
    private static final Map<String, TestEnvironment> repository = new HashMap<>();

    private TestEnvironment() {
        symbolicTrees = new HashMap<String, IExecutionStartNode>();
    }

    public static synchronized TestEnvironment loadEnvironmentForDirectory(
            String directory, boolean includeSubdirectories)
            throws KeYInterfaceException, IOException {

        if (repository.containsKey(directory)) {
            return repository.get(directory);
        }

        /*
         * Get the corresponding KeyJavaClass instances for each sourcefile in
         * the target directory.
         */
        List<File> javaFiles = loadAllJavaFilesInDirectory(directory,
                includeSubdirectories);
        List<KeYJavaClass> keYJavaClasses = loadKeYJavaFiles(javaFiles);

        /*
         * Symbolically execute all methods, and prepare the mapping.
         */
        Map<String, IExecutionStartNode> trees = new HashMap<>();
        for (KeYJavaClass keYJavaClass : keYJavaClasses) {
            for (String methoIdentifier : keYJavaClass.getMethods()) {
                KeYJavaMethod method = keYJavaClass.getMethod(methoIdentifier);
                if (!isNativeMethod(method)) {
                    IExecutionStartNode tree = keYInterface.getSymbolicExecutionTree(method);
                    Assert.assertNotNull(tree);
                    trees.put(methoIdentifier, tree);
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
    private final Map<String, IExecutionStartNode> symbolicTrees;

    private TestEnvironment(Map<String, IExecutionStartNode> trees) {
        this.symbolicTrees = trees;
    }

    /**
     * Getsthe symbolic execution tree for a given method.
     * 
     * @param identifier
     * @return
     */
    public IExecutionStartNode getSymbolicTreeForNode(String identifier) {
        return symbolicTrees.get(identifier);
    }

    /**
     * Gets file handlers for all Java files in a directory.
     * 
     * @param directory
     * @param includeSubdirectories
     * @return
     */
    protected static List<File> loadAllJavaFilesInDirectory(String directory,
            boolean includeSubdirectories) {
        List<File> results = new LinkedList<>();

        String path = keYTestGenPath + targetModelsPath + directory;
        File folder = new File(path);
        File[] files = folder.listFiles();
        for (int i = 0; i < files.length; i++) {
            File file = files[i];
            Assert.assertNotNull(file);

            /*
             * If the file is an ordinary file, add it iff it is a Java file.
             */
            if (file.isFile()) {
                if (file.getName().endsWith(".java")) {
                    Assert.assertTrue(file.canRead());
                    results.add(files[i]);
                }
            }

            /*
             * If it is a directory and we have the includeSubdirectories flag
             * set, add all files from the subdirectory.
             */
            else if (file.isDirectory() && includeSubdirectories) {
                String subpath = directory + File.separator + file.getName()
                        + File.separator;
                List<File> filesFromSubdirectory = loadAllJavaFilesInDirectory(
                        subpath, includeSubdirectories);
                results.addAll(filesFromSubdirectory);
            }
        }
        return results;
    }

    /**
     * Load a set of corresponding {@link KeYJavaClass} instances for a set of
     * legitimate Java files.
     * 
     * @param javaFiles
     *            the java files
     * @return the KeY abstractions
     * @throws KeYInterfaceException
     * @throws IOException
     */
    protected static List<KeYJavaClass> loadKeYJavaFiles(List<File> javaFiles)
            throws KeYInterfaceException, IOException {

        List<KeYJavaClass> keYJavaClasses = new LinkedList<>();
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
