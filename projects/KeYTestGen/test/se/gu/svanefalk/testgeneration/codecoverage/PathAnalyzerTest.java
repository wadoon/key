package se.gu.svanefalk.testgeneration.codecoverage;

import java.io.IOException;

import org.junit.Test;

import se.gu.svanefalk.testgeneration.KeYTestGenTest;
import se.gu.svanefalk.testgeneration.core.model.ModelGeneratorException;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class PathAnalyzerTest extends KeYTestGenTest {

    private final String containerTypeName = "PrimitiveIntegerOperations";
    private final String javaPathInBaseDir = "system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java";

    private SymbolicExecutionEnvironment<CustomConsoleUserInterface> getEnvironmentForMethod(
            final String method) throws ProofInputException,
            ModelGeneratorException, IOException, ProblemLoaderException {

        return getPreparedEnvironment(
                AbstractSymbolicExecutionTestCase.keyRepDirectory,
                javaPathInBaseDir, containerTypeName, method, null, false);
    }

    @Test
    public void test() throws ProofInputException, ModelGeneratorException,
            IOException, ProblemLoaderException {

        final String method = "max";
        final SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment = getEnvironmentForMethod(method);

        final SpecificationRepository repo = environment.getServices().getSpecificationRepository();
        final IExecutionStartNode root = environment.getBuilder().getStartNode();
        final IExecutionMethodCall callNode = getMethodCallNode(root);
        final KeYMediator mediator = environment.getBuilder().getMediator();
        final JavaInfo info = mediator.getJavaInfo();
        final IProgramMethod programMethod = callNode.getProgramMethod();

        System.out.println(callNode);
        System.out.println(callNode.getProgramMethod());
        final KeYJavaType container = callNode.getProgramMethod().getContainerType();
        System.out.println(container);

        /*
         * for(KeYJavaType type : info.getAllKeYJavaTypes()) {
         * System.out.println(type); }
         * 
         * int i = 0; for(Contract contract : repo.getAllContracts()) {
         * System.out.println(contract.getKJT()); System.out.println(i++); }
         */

        System.out.println("TYPE: "
                + info.getTypeByClassName("PrimitiveIntegerOperations"));
        System.out.println(info.getTypeByName("se.gu.svanefalk.testgeneration.targetmodels.PrimitiveIntegerOperations"));
        System.out.println(programMethod.getType());
        final KeYJavaType methodType = programMethod.getType();
        for (final FunctionalOperationContract contract : repo.getOperationContracts(
                methodType, callNode.getProgramMethod())) {
            System.out.println(contract);
        }
    }
}
