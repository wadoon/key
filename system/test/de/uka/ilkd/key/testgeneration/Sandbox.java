package de.uka.ilkd.key.testgeneration;

import java.io.IOException;
import java.util.ArrayList;

import org.junit.Test;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.testgeneration.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.parsers.PathconditionParser;
import de.uka.ilkd.key.testgeneration.xml.XMLGeneratorException;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class Sandbox
        extends KeYTestGenTest {

    private final String javaPathInBaseDir =
            "system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java";
    private final String containerTypeName = "PrimitiveIntegerOperations";

    @Test
    public void test()
            throws ProofInputException, ModelGeneratorException, IOException,
            XMLGeneratorException {

        KeYJavaType type = new KeYJavaType();
        
        ProgramElementName name = new ProgramElementName("self");
        LocationVariable var = new LocationVariable(name, type);
        
        System.out.println(var);
        // String method = "midOneProxyOneInstance";
        
        String method = "references";
        SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment =
                getEnvironmentForMethod(method);

        //printSymbolicExecutionTree(environment.getBuilder().getStartNode());
        
        ArrayList<IExecutionNode> nodes =
                retrieveNode(environment.getBuilder().getStartNode(), "return 1");

        Term nodeCondition = nodes.get(0).getPathCondition();
        TestCaseGenerator testCaseGenerator = TestCaseGenerator.getDefaultInstance();
        for (IExecutionNode node : nodes) {
            printSingleNode(node);
            PathconditionParser.createModel(node.getPathCondition(),
                    node.getServices());
            // modelgeneratingParser.createModel(node.getPathCondition(), node.getServices());
        }
    }

    private SymbolicExecutionEnvironment<CustomConsoleUserInterface> getEnvironmentForMethod(
            String method)
            throws ProofInputException, ModelGeneratorException, IOException {

        return getPreparedEnvironment(keyRepDirectory, javaPathInBaseDir,
                containerTypeName, method, null, false);

    }
}