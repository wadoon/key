package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.File;
import java.io.IOException;
import java.util.*;

/**
 * Method
 * {@link #createRunAllProofsTestUnits()} can be used to create a {@link List}
 * of {@link ProofGroup}s from an object of this class.
 *
 * @author Kai Wallisch
 */
public class ProofCollection {
    private final List<ProofGroup> units = new LinkedList<>();
    private ProofCollectionSettings settings = new ProofCollectionSettings();

    public ProofGroup addGroup(String name) {
        ProofGroup g = new ProofGroup(name, getSettings());
        units.add(g);
        return g;
    }

    public ProofGroup loadable(String file) {
        return addGroup(new File(file).getName())
                .loadable(file);
    }

    public ProofGroup provable(String file) {
        return addGroup(new File(file).getName())
                .provable(file);
    }

    public ProofGroup notprovable(String file) {
        return addGroup(new File(file).getName())
                .notprovable(file);
    }

    /**
     * Create list of {@link ProofGroup}s from list of
     * {@link Group}s.
     *
     * @return A list of {@link ProofGroup}s.
     */
    public List<ProofGroup> createRunAllProofsTestUnits() {
        List<String> activeGroups = settings.getRunOnlyOn();
        List<ProofGroup> ret = new LinkedList<>();
        Set<String> testCaseNames = new LinkedHashSet<>();

        for (ProofGroup group : units) {
            if (activeGroups != null && !activeGroups.contains(group.getGroupName())) {
                continue;
            }

            final String proposedTestCaseName = group.getGroupName();
            String testCaseName = proposedTestCaseName;
            int counter = 0;
            while (testCaseNames.contains(testCaseName)) {
                counter++;
                testCaseName = proposedTestCaseName + "#" + counter;
            }
            testCaseNames.add(testCaseName);
            group.setGroupName(testCaseName);
            ret.add(group);
        }

        Set<String> enabledTestCaseNames = settings.getEnabledTestCaseNames();
        if (enabledTestCaseNames == null) {
            return ret;
        } else {
            ret.removeIf(unit -> !enabledTestCaseNames.contains(unit.getGroupName()));
            return ret;
        }
    }

    public ProofCollectionSettings getSettings() {
        return settings;
    }
}
