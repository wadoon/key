package se.gu.svanefalk.testgeneration;

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

import se.gu.svanefalk.testgeneration.backend.IFrameworkConverter;
import se.gu.svanefalk.testgeneration.backend.TestGenerator;
import se.gu.svanefalk.testgeneration.backend.TestGeneratorException;
import se.gu.svanefalk.testgeneration.backend.junit.JUnitConverter;
import se.gu.svanefalk.testgeneration.backend.xml.XMLGeneratorException;
import se.gu.svanefalk.testgeneration.core.codecoverage.ICodeCoverageParser;
import se.gu.svanefalk.testgeneration.core.codecoverage.implementation.StatementCoverageParser;
import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterface;
import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import se.gu.svanefalk.testgeneration.core.model.ModelGeneratorException;
import se.gu.svanefalk.testgeneration.util.Benchmark;
import de.uka.ilkd.key.proof.init.ProofInputException;

public class TestJUnitTestCaseGenerator {

    @Test
    public void test() throws IOException, ProofInputException,
            ModelGeneratorException, TestGeneratorException,
            KeYInterfaceException, XMLGeneratorException, InterruptedException {

        Assert.assertTrue(new File(
                "/home/christopher/git/key/projects/KeYTestGen/test/se/gu/svanefalk/testgeneration/targetmodels/PrimitiveIntegerOperations.java").exists());

        final TestGenerator testCaseGenerator = TestGenerator.INSTANCE;
        final IFrameworkConverter junitConverter = new JUnitConverter();
        final ICodeCoverageParser codeCoverageParser = ICodeCoverageParser.decisionCoverageParser;

        final HashMap<String, Double> results = new HashMap<String, Double>();

        final String methodName = "midOneProxyOneInstance";
        final List<String> output = testCaseGenerator.generatePartialTestSuite(
                "/home/christopher/git/key/projects/KeYTestGen/test/se/gu/svanefalk/testgeneration/targetmodels/PrimitiveIntegerOperations.java",
                codeCoverageParser, junitConverter, "doStuff");

        /*
         * String output = testCaseGenerator .generatePartialTestSuite(
         * "/home/christopher/workspace/Key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java"
         * , null, "midOneProxyOneInstance");
         */

        /*
         * Discard outliers
         */

        final PriorityQueue<String> queue = new PriorityQueue<String>();
        final HashMap<String, Long> readings = Benchmark.getReadings();
        for (final String name : readings.keySet()) {
            queue.add(name);
        }
        while (!queue.isEmpty()) {
            final String next = queue.poll();
            final Long value = readings.get(next);

            System.out.println(next + " : " + value + " milliseconds");

            final double formatted = value;
            results.put(next, formatted / 1000);
        }

        System.out.println();
        Benchmark.reset();
        KeYInterface.getInstance().__DEBUG_RESET();

        System.out.println("RESULTS:");
        for (final String id : results.keySet()) {
            final double value = results.get(id);
            System.out.println(id + " : " + value + " milliseconds");
        }

        final String toWrite = output.get(0);
        System.out.println(toWrite);
        final File target = new File(
                "/home/christopher/git/key/eclipse/system/test/PrimitiveIntegerOperationsTestClass/Test_PrimitiveIntegerOperations_"
                        + methodName + ".java");
        final BufferedWriter bufferedWriter = new BufferedWriter(
                new FileWriter(target));
        bufferedWriter.write(toWrite);
        bufferedWriter.close();

    }

    @Ignore
    @Test
    public void test2() throws IOException, ProofInputException,
            ModelGeneratorException, TestGeneratorException,
            KeYInterfaceException, XMLGeneratorException, InterruptedException {

        Assert.assertTrue(new File(
                "/home/christopher/git/key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java").exists());

        final TestGenerator testCaseGenerator = TestGenerator.INSTANCE;
        final IFrameworkConverter junitConverter = new JUnitConverter();
        final ICodeCoverageParser codeCoverageParser = new StatementCoverageParser();

        final int RUNS = 100;
        final HashMap<String, Double> results = new HashMap<String, Double>();

        for (int i = 0; i < RUNS; i++) {

            testCaseGenerator.generatePartialTestSuite(
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

            final PriorityQueue<String> queue = new PriorityQueue<String>();
            final HashMap<String, Long> readings = Benchmark.getReadings();
            for (final String name : readings.keySet()) {
                queue.add(name);
            }
            while (!queue.isEmpty()) {
                final String next = queue.poll();
                final Long value = readings.get(next);

                System.out.println(next + " : " + value + " milliseconds");

                final double formatted = value;
                results.put(next, formatted / 1000);
            }

            System.out.println();
            Benchmark.reset();
            KeYInterface.getInstance().__DEBUG_RESET();
        }

        System.out.println("RESULTS:");
        for (final String id : results.keySet()) {
            final double value = results.get(id);
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
}