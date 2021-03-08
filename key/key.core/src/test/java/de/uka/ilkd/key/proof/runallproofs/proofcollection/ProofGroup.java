package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest;
import de.uka.ilkd.key.proof.runallproofs.TestResult;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

/**
 * A single unit that will be tested during {@link RunAllProofsTest} run.
 *
 * @author Kai Wallisch
 */
public final class ProofGroup {
    /**
     * The name of this test.
     */
    private String groupName;

    private final ProofCollectionSettings settings;
    private final List<ProofTest> proofTests = new LinkedList<>();

    public ProofCollectionSettings getSettings() {
        return settings;
    }

    public List<ProofTest> getProofTests() {
        return proofTests;
    }

    /**
     * Method {@link Object#toString()} is used by class {@link RunAllProofsTest}
     * to determine the name of a test case. It is overridden here so that test
     * cases can be easily recognized by their name.
     */
    @Override
    public String toString() {
        return groupName;
    }

    public ProofGroup(String name, ProofCollectionSettings settings) {
        this.groupName = name;
        this.settings = new ProofCollectionSettings(settings);
    }

    public boolean isSingleton() {
        return proofTests.size() <= 1;
    }

    /**
     * Run the test of this unit and return a {@link TestResult}.
     * <p>
     * If {@link #isSingleton()} is true, the result is the result of that single
     * test. Otherwise all results are aggregated into a single testresult.
     * <p>
     * The way of execution is determined by the {@link #settings}, in
     * particular by the {@link ProofCollectionSettings#getForkMode() forkmode}.
     *
     * @return either a single test result or an aggregated test result, not
     * <code>null</code>.
     */
    public TestResult runTests() throws Exception {
        if (proofTests.isEmpty())
            return new TestResult("Empty Group", true);

        /*
         * List of test results containing one test result for each test
         * file contained in this group.
         */
        List<TestResult> testResults;

        boolean verbose = settings.isVerbose();
        if (verbose) {
            System.out.println("Running test " + groupName);
        }

        boolean ignoreTest = settings.isIgnore();
        if (ignoreTest) {
            if (verbose) {
                System.out.println("... ignoring this test due to 'ignore=true' in file");
            }
            return new TestResult("Test case has been ignored", true);
        }

        ForkMode forkMode = settings.getForkMode();
        switch (forkMode) {
            case PERGROUP:
                testResults = ForkedTestFileRunner.processTestFiles(proofTests, getTempDir());
                break;

            case NOFORK:
                testResults = new ArrayList<>();
                for (ProofTest proofTest : proofTests) {
                    TestResult testResult = proofTest.runKey();
                    testResults.add(testResult);
                }
                break;

            case PERFILE:
                testResults = new ArrayList<>();
                for (ProofTest proofTest : proofTests) {
                    TestResult testResult =
                            ForkedTestFileRunner.processTestFile(proofTest, getTempDir());
                    testResults.add(testResult);
                }
                break;

            default:
                throw new RuntimeException("Unexpected value for fork mode: " + forkMode);
        }

        if (verbose) {
            System.out.format("Returning from test %s\n", groupName);
        }

        /*
         * Merge list of test results into one single test result, unless it is a
         * singleton case outside any group declaration.
         */
        if (isSingleton()) {
            assert testResults.size() == 1 : "Ungrouped test runs must have one case";
            return testResults.get(0);
        }

        boolean success = true;
        StringBuilder message = new StringBuilder("group " + groupName + ":\n");
        for (TestResult testResult : testResults) {
            success &= testResult.success;
            message.append(testResult.message).append("\n");
        }
        return new TestResult(message.toString(), success);
    }

    public String getGroupName() {
        return groupName;
    }

    /*
     * Temporary directory used by this test unit to store serialized data when
     * running in fork mode.
     */
    private Path tempDir = null;

    public Path getTempDir() throws IOException {
        File runAllProofsTempDir = settings.getTempDir();
        if (tempDir == null) {
            if (!runAllProofsTempDir.exists()) {
                runAllProofsTempDir.mkdirs();
            }
            tempDir = Files.createTempDirectory(runAllProofsTempDir.toPath(),
                    groupName + "-");
        }
        return tempDir;
    }

    private String localDirectory = "";

    public ProofGroup provable(String fileName) {
        ProofTest file = new ProofTest(ProofTest.TestProperty.PROVABLE, localDirectory + fileName,
                new ProofCollectionSettings(settings));
        proofTests.add(file);
        return this;
    }

    public ProofGroup notprovable(String fileName) {
        ProofTest file = new ProofTest(ProofTest.TestProperty.NOT_PROVABLE, localDirectory + fileName,
                new ProofCollectionSettings(settings));
        proofTests.add(file);
        return this;
    }

    public ProofGroup localSettings(String s) {
        settings.setLocalKeYSettings(s);
        return this;
    }

    public ProofGroup loadable(String fileName) {
        ProofTest file = new ProofTest(ProofTest.TestProperty.PROVABLE, localDirectory + fileName,
                new ProofCollectionSettings(settings));
        proofTests.add(file);
        return this;
    }

    public ProofGroup directory(String s) {
        localDirectory = s;
        return this;
    }

    public void setGroupName(String name) {
        groupName = name;
    }

    /**
     * Applies the given settings on the last added test
     * @return
     */
    public ProofGroup withSettings(String s) {
        ProofTest last = proofTests.get(proofTests.size() - 1);
        last.getSettings().setLocalKeYSettings(s);
        return this;
    }
}
