package com.csvanefalk.keytestgen;

import com.csvanefalk.keytestgen.backend.IFrameworkConverter;
import com.csvanefalk.keytestgen.backend.ITestSuite;
import com.csvanefalk.keytestgen.backend.TestGenerator;
import com.csvanefalk.keytestgen.backend.TestGeneratorException;
import com.csvanefalk.keytestgen.backend.junit.JUnitConverter;
import com.csvanefalk.keytestgen.backend.xml.XMLGeneratorException;
import com.csvanefalk.keytestgen.core.codecoverage.ICodeCoverageParser;
import com.csvanefalk.keytestgen.core.codecoverage.implementation.StatementCoverageParser;
import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.core.model.ModelGeneratorException;
import com.csvanefalk.keytestgen.util.Benchmark;
import de.uka.ilkd.key.proof.init.ProofInputException;
import org.junit.Assert;
import org.junit.Ignore;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.PriorityQueue;

public class TestJUnitTestCaseGenerator {

    @Ignore
    @Test
    public void test() throws IOException, ProofInputException, ModelGeneratorException, TestGeneratorException, KeYInterfaceException, XMLGeneratorException, InterruptedException {

        Assert.assertTrue(new File(
                "/home/christopher/git/key/projects/KeYTestGen/test/se/gu/svanefalk/testgeneration/targetmodels/ObjectClass.java")
                                  .exists());

        final TestGenerator testCaseGenerator = TestGenerator.getInstance();
        final IFrameworkConverter junitConverter = JUnitConverter.getInstance();
        final ICodeCoverageParser codeCoverageParser = ICodeCoverageParser.statementCoverageParser;

        final HashMap<String, Double> results = new HashMap<String, Double>();

        final String methodName = "max";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);
        final List<ITestSuite> output = testCaseGenerator.generateTestSuite(
                "/home/christopher/git/key/projects/KeYTestGen/test/se/gu/svanefalk/testgeneration/targetmodels/ObjectClass.java",
                codeCoverageParser,
                junitConverter,
                methods);

        /*
         * String output = testCaseGenerator .generatePartialTestSuite(
         * "/home/christopher/workspace/Key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java"
         * , null, "midOneProxyOneInstance");
         */

        /*
         * Discard outliers
         */
        for (ITestSuite testSuite : output) {
            System.out.println(testSuite.getTestSuiteBody());
        }

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

        System.out.println("RESULTS:");
        for (final String id : results.keySet()) {
            final double value = results.get(id);
            System.out.println(id + " : " + value + " milliseconds");
        }
    }

    @Ignore
    @Test
    public void test2() throws IOException, ProofInputException, ModelGeneratorException, TestGeneratorException, KeYInterfaceException, XMLGeneratorException, InterruptedException {

        Assert.assertTrue(new File(
                "/home/christopher/git/key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java")
                                  .exists());

        final TestGenerator testCaseGenerator = TestGenerator.getInstance();
        final IFrameworkConverter junitConverter = JUnitConverter.getInstance();
        final ICodeCoverageParser codeCoverageParser = new StatementCoverageParser();

        final int RUNS = 100;
        final HashMap<String, Double> results = new HashMap<String, Double>();

        String methodName = "mid";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);

        for (int i = 0; i < RUNS; i++) {

            testCaseGenerator.generateTestSuite(
                    "/home/christopher/git/key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java",
                    codeCoverageParser,
                    junitConverter,
                    methods);

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