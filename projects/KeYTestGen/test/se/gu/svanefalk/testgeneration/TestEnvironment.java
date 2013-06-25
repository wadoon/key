package se.gu.svanefalk.testgeneration;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.net.URL;
import java.util.HashMap;
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

    private static final File pathToExamples;
    private static TestEnvironment instance = null;

    /**
     * Creates the temporary oracle directory if required.
     */
    static {

        String path = TestEnvironment.class.getProtectionDomain().getCodeSource().getLocation().getPath();
        String[] pathElements = path.split(File.separator);
        int keyIndex = 0;
        final String dir = System.getProperty("user.dir");
        System.out.println("current dir = " + dir);
        /*
        for (int i = pathElements.length - 1; i >= 0; i--) {
            if(pathElements[i].)
        }
        System.out.println(location.getFile());
*/
        pathToExamples = null;
        Assert.assertTrue(pathToExamples != null);
        Assert.assertTrue(pathToExamples.exists());
        Assert.assertTrue(pathToExamples.canRead());
    }

    public static TestEnvironment getInstance(String path)
            throws KeYInterfaceException, IOException {
        if (TestEnvironment.instance == null) {

            /*
             * Get a handler to the test file.
             */
            File javaFile = new File(path);
            KeYJavaClass javaClass = KeYJavaClassFactory.getInstance().createKeYJavaClass(
                    javaFile);

            Map<String, IExecutionStartNode> trees = new HashMap<>();
            KeYInterface keYInterface = KeYInterface.getInstance();
            for (String methoIdentifier : javaClass.getMethods()) {

                KeYJavaMethod method = javaClass.getMethod(methoIdentifier);
                IExecutionStartNode tree = keYInterface.getSymbolicExecutionTree(method);
                trees.put(methoIdentifier, tree);
            }

            TestEnvironment.instance = new TestEnvironment(trees);
        }
        return TestEnvironment.instance;
    }

    private final Map<String, IExecutionStartNode> symbolicTrees;

    private TestEnvironment(Map<String, IExecutionStartNode> trees) {
        this.symbolicTrees = trees;
    }

    public IExecutionStartNode getSymbolicTreeForNode(String identifier) {
        return symbolicTrees.get(identifier);
    }

    /**
     * Helper for loading files
     * 
     * @param example
     * @return
     */
    private File loadFile(String example) {
        File file = new File(pathToExamples + example);
        Assert.assertTrue(file.exists());
        return file;
    }
}
