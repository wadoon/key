package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest;
import de.uka.ilkd.key.util.Pair;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.io.IOException;
import java.io.Serializable;
import java.util.*;

import static de.uka.ilkd.key.proof.runallproofs.proofcollection.TestFile.getAbsoluteFile;

/**
 * Immutable settings type for proof collections. Specifies settings used during test run of
 * {@link RunAllProofsTest}.
 *
 * @author Kai Wallisch
 */
public class ProofCollectionSettings implements Serializable {

    private static final long serialVersionUID = 8098789985911604781L;

    /*
     * Known constants for entries that may occur in field settingsMap.
     */
    private static final String BASE_DIRECTORY_KEY = "baseDirectory";
    private static final String KEY_SETTINGS_KEY = "keySettings";
    private static final String LOCAL_SETTINGS_KEY = "localSettings";
    private static final String FORK_MODE = "forkMode";
    private static final String STATISTICS_FILE = "statisticsFile";
    private static final String RELOAD_ENABLED = "reloadEnabled";
    private static final String TEMP_DIR = "tempDir";
    private static final String RUN_ONLY_ON = "runOnlyOn";
    private static final String DIRECTORY = "directory";
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofCollectionSettings.class);


    /**
     * The time at which the corresponding runallproofs run has been started.
     */
    public final Date runStart;

    /**
     * File in which the present {@link ProofCollectionSettings} were declared.
     */
    private final File sourceProofCollectionFile;

    /**
     * String {@link Map} containing all settings entries.
     */
    private final Map<String, String> immutableSettingsMap;

    /**
     * File in which statistics are written.
     */
    private final StatisticsFile statisticsFile;

    /**
     * {@link List} of settings entries that are created from system properties. Those entries are
     * copied into every {@link ProofCollectionSettings} object. Every system property starting with
     * "key.runallproofs." is considered a RunAllProofs setting. It overrides settings specified in
     * the automaticJAVADL.txt index file. RunAllProofs settings can be specified via system
     * properties by providing JVM arguments like: "-Dkey.runallproofs.forkMode=perFile"
     */
    private static final List<Pair<String, String>> SYSTEM_PROPERTIES_ENTRIES;

    static {
        /*
         * Iterating over all system properties to get settings entries. System properties starting
         * with "key.runallproofs." are relevant for proof collection settings.
         */
        List<Pair<String, String>> tmp = new LinkedList<>();
        Set<Map.Entry<Object, Object>> entrySet = System.getProperties().entrySet();
        for (var entry : entrySet) {
            String key = (String) entry.getKey();
            String value = (String) entry.getValue();
            if (key.startsWith("key.runallproofs.")) {
                key = key.substring(17);// strip "key.runallproofs." from key
                tmp.add(new Pair<>(key, value));
            }
        }
        SYSTEM_PROPERTIES_ENTRIES = Collections.unmodifiableList(tmp);
    }

    /**
     * Creates a {@link ProofCollectionSettings} object from the specified parameters with no parent
     * settings.
     */
    public ProofCollectionSettings(String proofCollectionFileLocation, List<Pair<String, String>> entries,
                                   Date runStart) {
        this.runStart = runStart;

        /*
         * Determine source proof collection file from string location.
         */
        assert proofCollectionFileLocation != null : "Unexpected nullpointer detected - "
                + "no proof collection source file specified.";
        sourceProofCollectionFile = new File(proofCollectionFileLocation).getParentFile();
        assert sourceProofCollectionFile.isAbsolute()
                : "Expecting location of source proof collection "
                + "file to be given as absolute path.";
        assert sourceProofCollectionFile.exists()
                : "Given source proof collection file does not exist.";

        /*
         * Compute immutable map containing settings entries.
         */
        var settings = Pair.toMap(SYSTEM_PROPERTIES_ENTRIES);
        settings.putAll(Pair.toMap(entries));
        immutableSettingsMap = Collections.unmodifiableMap(settings);

        /*
         * Compute location of statistics file.
         */
        String statisticsFileName = get(STATISTICS_FILE);
        if (statisticsFileName == null) {
            statisticsFile = null;
        } else {
            statisticsFile =
                    new StatisticsFile(getAbsoluteFile(getBaseDirectory(), statisticsFileName));
        }
    }

    /**
     * Creates a {@link ProofCollectionSettings} object that overrides an existing
     * {@link ProofCollectionSettings} object.
     */
    public ProofCollectionSettings(ProofCollectionSettings parentSettings, List<Pair<String, String>> entries) {
        this.runStart = parentSettings.runStart;

        /*
         * Use source proof collection from parent settings.
         */
        this.sourceProofCollectionFile = parentSettings.sourceProofCollectionFile;
        var local = Pair.toMap(entries);
        var parent = new HashMap<>(parentSettings.immutableSettingsMap);
        parent.putAll(local);
        immutableSettingsMap = Collections.unmodifiableMap(parent);

        /*
         * Inherit statistics file from parent settings.
         */
        statisticsFile = parentSettings.getStatisticsFile();
    }

    /**
     * Reads out generic settings, which were be specified as (key, value) pairs during object
     * creation.
     *
     * @see Entry
     */
    public String get(String key) {
        return immutableSettingsMap.get(key);
    }

    public ForkMode getForkMode() {

        ForkMode forkMode = null;
        String forkModeString = get(FORK_MODE);

        if (forkModeString == null || forkModeString.length() == 0) {
            // Return default value in case no particular fork mode is
            // specified.
            forkMode = ForkMode.NOFORK;
        } else {
            for (ForkMode mode : ForkMode.values()) {
                if (mode.settingName.equalsIgnoreCase(forkModeString)) {
                    forkMode = mode;
                    break;
                }
            }
        }

        /*
         * Warn user that specified fork mode was not recognized but use default fork mode rather
         * than throwing an Exception.
         */
        if (forkMode == null) {
            /*
             * Unknown value used for fork mode. Printing out warning to the user.
             */
            LOGGER.warn("Warning: Unknown value used for runAllProofs fork mode:  {}",
                    forkModeString);
            LOGGER.warn("Use either of the following: noFork (default), perGroup, perFile");
            LOGGER.warn("Using default fork mode: noFork");
            LOGGER.warn("If you want to inspect source code, look up the following location:");
            LOGGER.warn("{}", new Throwable().getStackTrace()[0]);
            forkMode = ForkMode.NOFORK;
        }

        return forkMode;
    }

    /**
     * Returns KeY settings that will be used as default settings.
     */
    public String getGlobalKeYSettings() {
        String gks = get(KEY_SETTINGS_KEY);
        return gks == null ? "" : gks;
    }

    /**
     * Returns the KeY settings modified locally in the group.
     *
     * @return <code>null</code> if not set, otherwise the local settings
     */
    public String getLocalKeYSettings() {
        return get(LOCAL_SETTINGS_KEY);
    }

    /**
     * Settings must specify a base directory. Relative {@link ProofCollectionSettings} paths will
     * be treated as relative to directory returned by this method.
     */
    public File getBaseDirectory() {
        String baseDirectoryName = get(BASE_DIRECTORY_KEY);
        return baseDirectoryName == null ? sourceProofCollectionFile.getParentFile()
                : getAbsoluteFile(sourceProofCollectionFile, baseDirectoryName);
    }

    /**
     * Returns location of statistics file. Can be null. In this case no statistics are saved.
     */
    public StatisticsFile getStatisticsFile() {
        return statisticsFile;
    }

    public File getTempDir() throws IOException {
        String tempDirString = get(TEMP_DIR);
        if (tempDirString == null) {
            throw new IOException(
                    "No temporary directory specified in RunAllProofs configuration file. "
                            + "Cannot run in forked mode. " + "To solve this, specify setting \"" + TEMP_DIR
                            + "\" in file " + sourceProofCollectionFile);
        }
        File tempDir = new File(tempDirString);
        if (!tempDir.isAbsolute()) {
            tempDir = new File(getBaseDirectory(), tempDirString);
        }
        if (tempDir.isFile()) {
            throw new IOException("Specified temporary directory is a file: " + tempDir + "\n"
                    + "Configure temporary directory in file " + sourceProofCollectionFile
                    + " to solve this.");
        }
        return tempDir;
    }

    /**
     * Retrieve names of test cases that are configured to be enabled. By default, all
     * {@link RunAllProofsTest} test cases are enabled. If this method returns something else than
     * null, then only test cases whose name is contained in the returned set are enabled.
     */
    public Set<String> getEnabledTestCaseNames() {
        String testCases = get("testCases");
        if (testCases == null || testCases.length() == 0) {
            return null;
        }

        Set<String> enabledTestCaseNames = new LinkedHashSet<>();
        String[] testCaseList = testCases.split(",");
        Collections.addAll(enabledTestCaseNames, testCaseList);
        enabledTestCaseNames = Collections.unmodifiableSet(enabledTestCaseNames);
        return enabledTestCaseNames;
    }

    /**
     * Check whether proof reloading is enabled or disabled. If enabled, closed proofs will be saved
     * and reloaded after prover is finished.
     */
    public boolean reloadEnabled() {
        String reloadEnabled = get(RELOAD_ENABLED);
        if (reloadEnabled == null || reloadEnabled.equals("true") || reloadEnabled.equals("")) {
            return true;
        } else if (reloadEnabled.equals("false")) {
            return false;
        } else {
            LOGGER.warn("Warning - unrecognized reload option: {}", reloadEnabled);
            return true;
        }
    }

    /**
     * Gets the list of groups on which the test should be run.
     *
     * <code>null</code> means all of them, otherwise a list of group names
     *
     * @return <code>null</code> or a list.
     */
    public List<String> getRunOnlyOn() {
        String runOnly = get(RUN_ONLY_ON);
        if (runOnly == null) {
            return null;
        } else {
            return Arrays.asList(runOnly.trim().split(" *, *"));
        }
    }

    /**
     * Gets the directory for a group.
     * <p>
     * If the groups has its own directory key, take it into consideration, return the base
     * directory otherwise
     *
     * @return the directory for the current group.
     */
    public File getGroupDirectory() {
        String localDir = get(DIRECTORY);
        if (localDir != null) {
            return new File(getBaseDirectory(), localDir);
        } else {
            return getBaseDirectory();
        }
    }

}
