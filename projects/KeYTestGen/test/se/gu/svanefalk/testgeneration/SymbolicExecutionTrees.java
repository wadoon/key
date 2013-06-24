package se.gu.svanefalk.testgeneration;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;

import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaClass;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaClassFactory;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaMethod;
import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterface;
import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import se.gu.svanefalk.testgeneration.util.transformers.RemoveObserverFunctionsTransformer;

public class SymbolicExecutionTrees {

    private static SymbolicExecutionTrees instance = null;

    public static SymbolicExecutionTrees getInstance(String path)
            throws KeYInterfaceException, IOException {
        if (SymbolicExecutionTrees.instance == null) {

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

            SymbolicExecutionTrees.instance = new SymbolicExecutionTrees(trees);
        }
        return SymbolicExecutionTrees.instance;
    }

    private final Map<String, IExecutionStartNode> symbolicTrees;

    private SymbolicExecutionTrees(Map<String, IExecutionStartNode> trees) {
        this.symbolicTrees = trees;
    }

    public IExecutionStartNode getSymbolicTreeForNode(String identifier) {
        return symbolicTrees.get(identifier);
    }
}
