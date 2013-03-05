package de.uka.ilkd.key.testgeneration;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.PriorityQueue;

import org.junit.Assert;
import org.junit.Ignore;
import org.junit.Test;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.testgeneration.backend.IFrameworkConverter;
import de.uka.ilkd.key.testgeneration.backend.TestGenerator;
import de.uka.ilkd.key.testgeneration.backend.TestGeneratorException;
import de.uka.ilkd.key.testgeneration.backend.junit.JUnitConverter;
import de.uka.ilkd.key.testgeneration.backend.xml.XMLGeneratorException;
import de.uka.ilkd.key.testgeneration.core.codecoverage.ICodeCoverageParser;
import de.uka.ilkd.key.testgeneration.core.codecoverage.implementation.StatementCoverageParser;
import de.uka.ilkd.key.testgeneration.core.keyinterface.KeYInterface;
import de.uka.ilkd.key.testgeneration.core.keyinterface.KeYInterfaceException;
import de.uka.ilkd.key.testgeneration.core.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.util.Benchmark;

public class TestJUnitTestCaseGenerator {

    @Test
    public void test() throws IOException, ProofInputException,
            ModelGeneratorException, TestGeneratorException,
            KeYInterfaceException, XMLGeneratorException, InterruptedException {

        Assert.assertTrue(new File(
                "/home/christopher/git/key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java")
                .exists());

        TestGenerator testCaseGenerator = TestGenerator.INSTANCE;
        IFrameworkConverter junitConverter = new JUnitConverter();
        ICodeCoverageParser codeCoverageParser = new StatementCoverageParser();

        HashMap<String, Double> results = new HashMap<String, Double>();

        String methodName = "midOneProxyOneInstance";
        List<String> output = testCaseGenerator
                .generatePartialTestSuite(
                        "/home/christopher/git/key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java",
                        codeCoverageParser, junitConverter, methodName);

        /*
         * String output = testCaseGenerator .generatePartialTestSuite(
         * "/home/christopher/workspace/Key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java"
         * , null, "midOneProxyOneInstance");
         */

        /*
         * Discard outliers
         */

        PriorityQueue<String> queue = new PriorityQueue<String>();
        HashMap<String, Long> readings = Benchmark.getReadings();
        for (String name : readings.keySet()) {
            queue.add(name);
        }
        while (!queue.isEmpty()) {
            String next = queue.poll();
            Long value = readings.get(next);

            System.out.println(next + " : " + value + " milliseconds");

            double formatted = value;
            results.put(next, formatted / 1000);
        }

        System.out.println();
        Benchmark.reset();
        KeYInterface.INSTANCE.__DEBUG_RESET();

        System.out.println("RESULTS:");
        for (String id : results.keySet()) {
            double value = results.get(id);
            System.out.println(id + " : " + value + " milliseconds");
        }

        String toWrite = output.get(0);
        System.out.println(toWrite);
        File target = new File(
                "/home/christopher/git/key/eclipse/system/test/PrimitiveIntegerOperationsTestClass/Test_PrimitiveIntegerOperations_"
                        + methodName + ".java");
        BufferedWriter bufferedWriter = new BufferedWriter(new FileWriter(
                target));
        bufferedWriter.write(toWrite);
        bufferedWriter.close();

    }

    @Ignore
    @Test
    public void test2() throws IOException, ProofInputException,
            ModelGeneratorException, TestGeneratorException,
            KeYInterfaceException, XMLGeneratorException, InterruptedException {

        Assert.assertTrue(new File(
                "/home/christopher/git/key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java")
                .exists());

        TestGenerator testCaseGenerator = TestGenerator.INSTANCE;
        IFrameworkConverter junitConverter = new JUnitConverter();
        ICodeCoverageParser codeCoverageParser = new StatementCoverageParser();

        final int RUNS = 100;
        HashMap<String, Double> results = new HashMap<String, Double>();

        for (int i = 0; i < RUNS; i++) {

            List<String> output = testCaseGenerator
                    .generatePartialTestSuite(
                            "/home/christopher/git/key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java",
                            codeCoverageParser, junitConverter, "mid");

            /*
             * String output = testCaseGenerator .generatePartialTestSuite(
             * "/home/christopher/workspace/Key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java"
             * , null, "midOneProxyOneInstance");
             */

            /*
             * Discard outliers
             */

            PriorityQueue<String> queue = new PriorityQueue<String>();
            HashMap<String, Long> readings = Benchmark.getReadings();
            for (String name : readings.keySet()) {
                queue.add(name);
            }
            while (!queue.isEmpty()) {
                String next = queue.poll();
                Long value = readings.get(next);

                System.out.println(next + " : " + value + " milliseconds");

                double formatted = value;
                results.put(next, formatted / 1000);
            }

            System.out.println();
            Benchmark.reset();
            KeYInterface.INSTANCE.__DEBUG_RESET();
        }

        System.out.println("RESULTS:");
        for (String id : results.keySet()) {
            double value = results.get(id);
            System.out.println(id + " : " + value + " milliseconds");
        }

        /*
         * String toWrite = output.get(0); System.out.println(toWrite); File
         * target = new File(
         * "/home/christopher/git/key/eclipse/system/test/PrimitiveIntegerOperationsTestClass/Test_PrimitiveIntegerOperations_mid.java"
         * ); BufferedWriter bufferedWriter = new BufferedWriter(new
         * FileWriter(target)); bufferedWriter.write(toWrite);
         * bufferedWriter.close();
         */
    }

    private <T> T get(Object o) {
        return (T) o;
    }
}