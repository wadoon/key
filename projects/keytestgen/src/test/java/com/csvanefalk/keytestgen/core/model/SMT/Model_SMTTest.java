package com.csvanefalk.keytestgen.core.model.SMT;

import com.csvanefalk.keytestgen.backend.IFrameworkConverter;
import com.csvanefalk.keytestgen.backend.TestGenerator;
import com.csvanefalk.keytestgen.backend.TestGeneratorException;
import com.csvanefalk.keytestgen.backend.junit.JUnitConverter;
import com.csvanefalk.keytestgen.backend.xml.XMLGeneratorException;
import com.csvanefalk.keytestgen.core.codecoverage.ICodeCoverageParser;
import com.csvanefalk.keytestgen.core.codecoverage.implementation.StatementCoverageParser;
import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.core.model.ModelGeneratorException;
import de.uka.ilkd.key.proof.init.ProofInputException;

import java.io.IOException;
import java.util.Calendar;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

public class Model_SMTTest {

    public int counter = 0;

    //@Test
    public void test() throws IOException, ProofInputException, ModelGeneratorException, TestGeneratorException, KeYInterfaceException, XMLGeneratorException, InterruptedException {

        final TestGenerator testCaseGenerator = TestGenerator.getInstance();
        final IFrameworkConverter junitConverter = JUnitConverter.getInstance();
        final ICodeCoverageParser codeCoverageParser = new StatementCoverageParser();

        final HashMap<String, Double> results = new HashMap<String, Double>();
        List<String> methods = new LinkedList<String>();
        methods.add("mid");

        for (int i = 0; i < 100; i++) {
            long time = Calendar.getInstance().getTimeInMillis();

            final String methodName = "midOneProxyOneInstance";
            testCaseGenerator.generateTestSuite(
                    "/home/christopher/git/ktg_smt/key/projects/KeYTestGen/test/se/gu/svanefalk/testgeneration/targetmodels/PrimitiveIntegerOperations.java",
                    codeCoverageParser,
                    junitConverter,
                    methods);

            System.out.println("Trial: " + counter++);
            PaperTest.addResult("TOTAL", Calendar.getInstance().getTimeInMillis() - time);
        }

        PaperTest.printResults();
        
        /*
         * String output = testCaseGenerator .generatePartialTestSuite(
         * "/home/christopher/workspace/Key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java"
         * , null, "midOneProxyOneInstance");
         */

        /*
         * Discard outliers
         */
        /*
         * final PriorityQueue<String> queue = new PriorityQueue<String>();
         * final HashMap<String, Long> readings = Benchmark.getReadings(); for
         * (final String name : readings.keySet()) { queue.add(name); } while
         * (!queue.isEmpty()) { final String next = queue.poll(); final Long
         * value = readings.get(next);
         * 
         * System.out.println(next + " : " + value + " milliseconds");
         * 
         * final double formatted = value; results.put(next, formatted / 1000);
         * }
         * 
         * System.out.println(); Benchmark.reset();
         * KeYInterface.INSTANCE.__DEBUG_RESET();
         * 
         * System.out.println("RESULTS:"); for (final String id :
         * results.keySet()) { final double value = results.get(id);
         * System.out.println(id + " : " + value + " milliseconds"); }
         * 
         * final String toWrite = output.get(0); System.out.println(toWrite);
         * final File target = new File(
         * "/home/christopher/git/key/eclipse/system/test/PrimitiveIntegerOperationsTestClass/Test_PrimitiveIntegerOperations_"
         * + methodName + ".java"); final BufferedWriter bufferedWriter = new
         * BufferedWriter( new FileWriter(target));
         * bufferedWriter.write(toWrite); bufferedWriter.close();
         */

    }

}
