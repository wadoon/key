package de.uka.ilkd.key.testgeneration.codecoverage;

import java.io.IOException;
import java.util.LinkedList;

import org.junit.Test;

import z3parser.tree.bnf.Absyn.EBool;
import z3parser.tree.bnf.Absyn.Op;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.testgeneration.KeYTestGenTest;
import de.uka.ilkd.key.testgeneration.model.modelgeneration.ModelGeneratorException;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class PathAnalyzerTest
        extends KeYTestGenTest {

    private final String javaPathInBaseDir =
            "system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java";
    private final String containerTypeName = "PrimitiveIntegerOperations";

    @Test
    public void test() throws ProofInputException, ModelGeneratorException, IOException {

        String method = "max";
        SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment =
                getEnvironmentForMethod(method);

        SpecificationRepository repo = environment.getServices().getSpecificationRepository();
        IExecutionStartNode root = environment.getBuilder().getStartNode();
        IExecutionMethodCall callNode = getMethodCallNode(root);
        KeYMediator mediator = environment.getBuilder().getMediator();
        JavaInfo info = mediator.getJavaInfo();
        IProgramMethod programMethod = callNode.getProgramMethod();

        System.out.println(callNode);
        System.out.println(callNode.getProgramMethod());
        KeYJavaType container = callNode.getProgramMethod().getContainerType();
        System.out.println(container);

        /*
         * for(KeYJavaType type : info.getAllKeYJavaTypes()) { System.out.println(type); }
         * 
         * int i = 0; for(Contract contract : repo.getAllContracts()) {
         * System.out.println(contract.getKJT()); System.out.println(i++); }
         */

        System.out.println("TYPE: " + info.getTypeByClassName("PrimitiveIntegerOperations"));
        System.out.println(info.getTypeByName("de.uka.ilkd.key.testgeneration.targetmodels.PrimitiveIntegerOperations"));
        System.out.println(programMethod.getType());
        KeYJavaType methodType = programMethod.getType();
        for (FunctionalOperationContract contract : repo.getOperationContracts(methodType, callNode.getProgramMethod())) {
            System.out.println(contract);
        }
    }

    private SymbolicExecutionEnvironment<CustomConsoleUserInterface> getEnvironmentForMethod(
            String method) throws ProofInputException, ModelGeneratorException, IOException {

        return getPreparedEnvironment(keyRepDirectory, javaPathInBaseDir, containerTypeName,
                method, null, false);
    }
}
