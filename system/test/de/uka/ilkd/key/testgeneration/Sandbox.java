package de.uka.ilkd.key.testgeneration;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import z3parser.tree.bnf.Absyn.Modl;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.testgeneration.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.model.implementation.Model;
import de.uka.ilkd.key.testgeneration.model.implementation.ModelVariable;
import de.uka.ilkd.key.testgeneration.visitors.TermModelVisitor;
import de.uka.ilkd.key.testgeneration.xml.XMLGeneratorException;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class Sandbox
        extends KeYTestGenTest {

    private final String javaPathInBaseDir =
            "system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java";
    private final String containerTypeName = "PrimitiveIntegerOperations";

    @Test
    public void test() throws ProofInputException, ModelGeneratorException, IOException, XMLGeneratorException {

        
        String method = "midOneProxyOneInstance";
        SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment =
                getEnvironmentForMethod(method);

        ArrayList<IExecutionNode> nodes =
                retrieveNode(environment.getBuilder().getStartNode(), "mid=x");

        Term nodeCondition = nodes.get(0).getPathCondition();
        TermModelVisitor modelVisitor = new TermModelVisitor(nodes.get(0).getServices());

        TestCaseGenerator testCaseGenerator = TestCaseGenerator.getDefaultInstance();
        
    }

    private SymbolicExecutionEnvironment<CustomConsoleUserInterface> getEnvironmentForMethod(
            String method)
            throws ProofInputException, ModelGeneratorException, IOException {

        return getPreparedEnvironment(keyRepDirectory, javaPathInBaseDir,
                containerTypeName, method, null, false);
    
    }
}