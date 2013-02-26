package de.uka.ilkd.key.testgeneration;

import java.io.File;
import java.io.IOException;
import java.util.Collection;
import java.util.List;
import java.util.Scanner;

import org.junit.Test;

import com.sun.org.apache.bcel.internal.classfile.JavaClass;
import com.sun.org.apache.bcel.internal.generic.ClassGen;

import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.gui.smt.ProofDependentSMTSettings;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.reference.TypeReferenceImp;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.smt.IllegalFormulaException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.testgeneration.backend.xml.XMLGeneratorException;
import de.uka.ilkd.key.testgeneration.core.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.RemoveSDPsTransformer;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.TermTransformerException;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class Sandbox extends KeYTestGenTest {

    private final String javaPathInBaseDir = "system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java";
    private final String containerTypeName = "PrimitiveIntegerOperations";

    @Test
    public void test() throws ProofInputException, ModelGeneratorException,
            IOException, XMLGeneratorException, ProblemLoaderException,
            IllegalFormulaException, TermTransformerException {

        String method = "mid";
        SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment = getEnvironmentForMethod(method);

        List<IExecutionNode> nodes = retrieveNode(environment.getBuilder()
                .getStartNode(), "mid=x");

        for (IExecutionNode node : nodes) {

                System.out.println(node.getFormatedPathCondition());
        }
    }
   
    private SymbolicExecutionEnvironment<CustomConsoleUserInterface> getEnvironmentForMethod(
            String method) throws ProofInputException, ModelGeneratorException,
            IOException, ProblemLoaderException {

        return getPreparedEnvironment(keyRepDirectory, javaPathInBaseDir,
                containerTypeName, method, null, false);
    }

    /**
     * Settings to pass to the SMT solver.
     * 
     * @author christopher
     */
    private static class SMTSettings2 implements
            de.uka.ilkd.key.smt.SMTSettings {

        @Override
        public int getMaxConcurrentProcesses() {

            return 1;
        }

        @Override
        public int getMaxNumberOfGenerics() {

            return 2;
        }

        @Override
        public String getSMTTemporaryFolder() {

            return PathConfig.getKeyConfigDir() + File.separator
                    + "smt_formula";
        }

        @Override
        public Collection<Taclet> getTaclets() {

            return null;
        }

        @Override
        public long getTimeout() {

            return 5000;
        }

        @Override
        public boolean instantiateNullAssumption() {

            return true;
        }

        @Override
        public boolean makesUseOfTaclets() {

            return false;
        }

        @Override
        public boolean useExplicitTypeHierarchy() {

            return false;
        }

        @Override
        public boolean useBuiltInUniqueness() {

            return false;
        }

        @Override
        public boolean useAssumptionsForBigSmallIntegers() {

            return false;
        }

        @Override
        public boolean useUninterpretedMultiplicationIfNecessary() {

            return false;
        }

        @Override
        public long getMaximumInteger() {

            return ProofDependentSMTSettings.getDefaultSettingsData().maxInteger;
        }

        @Override
        public long getMinimumInteger() {

            return ProofDependentSMTSettings.getDefaultSettingsData().minInteger;
        }

        @Override
        public String getLogic() {

            return "AUFLIA";
        }

        @Override
        public boolean checkForSupport() {

            return false;
        }
    }
}