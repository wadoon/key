package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit;

import java.io.IOException;
import java.util.*;

/**
 * Method
 * {@link #createRunAllProofsTestUnits()} can be used to create a {@link List}
 * of {@link RunAllProofsTestUnit}s from an object of this class.
 *
 * @author Kai Wallisch
 */
public class ProofCollection {
    private final List<Group> units = new LinkedList<>();
    private ProofCollectionSettings settings = new ProofCollectionSettings();

    void add(Group unit) {
        units.add(unit);
    }

    protected RunAllProofsTestUnit addGroup(String name) {
        return new RunAllProofsTestUnit(name, getSettings(), new ArrayList<>(), false);
    }

    /**
     * Create list of {@link RunAllProofsTestUnit}s from list of
     * {@link Group}s.
     *
     * @return A list of {@link RunAllProofsTestUnit}s.
     * @throws IOException Names of {@link SingletonGroup}s are determined
     *                     by their corresponding file names. In case file name can't be
     *                     read {@link IOException} may be thrown.
     */
    public List<RunAllProofsTestUnit> createRunAllProofsTestUnits()
            throws IOException {

        List<String> activeGroups = settings.getRunOnlyOn();

        List<RunAllProofsTestUnit> ret = new LinkedList<>();
        Set<String> testCaseNames = new LinkedHashSet<>();
        for (Group group : units) {

            if (activeGroups != null && !activeGroups.contains(group.getName())) {
                continue;
            }

            final String proposedTestCaseName = group.getName();
            String testCaseName = proposedTestCaseName;
            int counter = 0;
            while (testCaseNames.contains(testCaseName)) {
                counter++;
                testCaseName = proposedTestCaseName + "#" + counter;
            }
            testCaseNames.add(testCaseName);

            RunAllProofsTestUnit testUnit = group
                    .createRunAllProofsTestUnit(testCaseName);
            ret.add(testUnit);
        }

        Set<String> enabledTestCaseNames = settings.getEnabledTestCaseNames();
        if (enabledTestCaseNames == null) {
            return ret;
        } else {
            Iterator<RunAllProofsTestUnit> iterator = ret.iterator();
            while (iterator.hasNext()) {
                RunAllProofsTestUnit unit = iterator.next();
                if (!enabledTestCaseNames.contains(unit.getTestName())) {
                    iterator.remove();
                }
            }
            return ret;
        }
    }

    public ProofCollectionSettings getSettings() {
        return settings;
    }
}
