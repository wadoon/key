
package de.uka.ilkd.key.testgeneration;

import java.io.ByteArrayInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.junit.Before;
import org.junit.Test;



import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.parser.KeYParser;
import de.uka.ilkd.key.parser.proofjava.ParseException;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.testgeneration.modelgeneration.IModelGenerator;
import de.uka.ilkd.key.testgeneration.modelgeneration.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.modelgeneration.IModelGenerator.IModelContainer;
import de.uka.ilkd.key.testgeneration.modelgeneration.ModelGenerator;
import de.uka.ilkd.key.testgeneration.targetmodels.PrimitiveIntegerOperations;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;


/**
 * Tests to assert that the model generation procedure generates fixtures 
 * whichindeed cause specified execution paths to be taken. 
 * 
 * IMPORTANT - these test cases involve heavy use of native program invocations,
 * and might take significant time to execute.
 * 
 * To achieve this, 
 * 
 * @author christopher
 *
 */
public class TestModelGenerationIntegers extends KeYTestGenTest {

    private IModelGenerator modelGenerator;
    private final String javaPathInBaseDir = "system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java";
    private final String containerTypeName = "PrimitiveIntegerOperations";

    private SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment;

    @Before
    public void setup() throws ModelGeneratorException {
        //modelGenerator = ModelGenerator.getDefaultModelGenerator();
    }

    @Test
    public  void testMidOneExternal() throws Exception {
        
       
        /*
         * THIS METHOD IS CURRENTLY ONLY USED FOR DEVELOPMENT
         */
        
        
        setup("midExperimental");
        
        //printSymbolicExecutionTreePathConditions( environment.getBuilder().getStartNode());

        
        

    
         ArrayList<IExecutionNode> nodes = retrieveNode(environment.getBuilder().getStartNode(), "mid=y");

        for(IExecutionNode node : nodes) {
            
            printSingleNode(node);
            
        }

            /*
            System.out.println(modelGenerator.generateNodeModel(node, node.getServices()));
            HashMap<String, ValueContainer> model = parseZ3Model(modelGenerator.generateNodeModel(node, node.getServices()));
            
            printModel(model);

            int x = (Integer)model.get("x").getValue();
            int y = (Integer)model.get("y").getValue();
            int z = (Integer)model.get("z").getValue();
            int result = PrimitiveIntegerOperations.mid(x,y,z);

            assertTrue(result == (Integer)model.get("y").getValue());
        }
        */
        
    }
    
    @Test
    public void testEasterDate() throws FileNotFoundException, ProofInputException, ModelGeneratorException {

        /*
         *No idea why this is broken, but broken it is.
         *
         * setup("easterDate");
         */
    }

    @Test
    public void testEuclides() throws FileNotFoundException, ProofInputException, ModelGeneratorException {

        /*
         * For recursion to work, we will need a different strategy setting. How we can infer
         * what strategy to be used, is not clear at this stage. 
         *
         * setup("euclides");
         */
    }

    /**
     * Tests that we are able to generate path conditions in such a way that all possible
     * return values for each input variable to mid() are taken.
     * @throws Exception 
     */
    @Test
    public void testMid() throws Exception {

        setup("mid");

        testMidReturn("x");
        testMidReturn("y");
        testMidReturn("z");
    }

    /**
     * Test various return values for the mid method. 
     * 
     * @param variable - can be x, y or z. See signature for mid.
     * @throws Exception 
     */
    private void testMidReturn(String variable) throws Exception {
              
        ArrayList<IExecutionNode> nodes = retrieveNode(environment.getBuilder().getStartNode(), "mid=" + variable);
        
        /*
         * For each node, generate a model for it, refine that model, and then use
         * the resulting fixture in order to run the method under test and assert correct
         * results. 
         */
        for(IExecutionNode node : nodes) {

            HashMap<String, IModelContainer> model = modelGenerator.generateModel(node);
            
            for(IModelContainer container : model.values()) {
                System.out.println(container);
            }
            

            int x = (Integer)model.get("x").getValue();
            int y = (Integer)model.get("y").getValue();
            int z = (Integer)model.get("z").getValue();
            int result = PrimitiveIntegerOperations.mid(x,y,z);

            assertTrue(result == (Integer)model.get(variable).getValue());
        }
    }

    private void setup(String method) throws ProofInputException, ModelGeneratorException, IOException {

        if (modelGenerator == null) {
            modelGenerator = ModelGenerator.getDefaultModelGenerator();
        }

        environment = getPreparedEnvironment(keyRepDirectory, 
                javaPathInBaseDir, 
                containerTypeName, 
                method, 
                null, 
                false);
    }
}