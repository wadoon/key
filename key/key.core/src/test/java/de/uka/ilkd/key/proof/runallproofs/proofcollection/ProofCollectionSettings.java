package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest;
import de.uka.ilkd.key.util.LinkedHashMap;

import java.io.File;
import java.io.IOException;
import java.io.Serializable;
import java.util.*;
import java.util.Map.Entry;

/**
 * Immutable settings type for proof collections. Specifies settings used during
 * test run of {@link RunAllProofsTest}.
 *
 * @author Kai Wallisch
 */
public class ProofCollectionSettings implements Serializable {
    /*
     * Known constants for entries that may occur in field settingsMap.
     */
    private static final String KEY_BASE_DIRECTORY = "baseDirectory";
    private static final String KEY_SETTINGS_KEY = "keySettings";
    private static final String KEY_VERBOSE = "verboseOutput";
    private static final String KEY_LOCAL_SETTINGS = "localSettings";
    private static final String KEY_FORK_MODE = "forkMode";
    private static final String KEY_STATISTICS_FILE = "statisticsFile";
    private static final String KEY_RELOAD_ENABLED = "reloadEnabled";
    private static final String KEY_TEMP_DIR = "tempDir";
    private static final String KEY_RUN_ONLY_ON = "runOnlyOn";
    private static final String KEY_DIRECTORY = "directory";
    public static final String IGNORE_KEY = "ignore";
    public static final String KEY_FORK_TIMEOUT = "forkTimeout";
    public static final String FORK_DEBUG_PORT = "forkDebugPort";
    private static final String KEY_FORK_MEMORY = "forkMemory";


    /**
     * The time at which the corresponding runallproofs run has been started.
     */
    public Date runStart;

    /**
     * String {@link Map} containing all settings entries.
     */
    private Map<String, String> settings = new HashMap<>();

    /**
     * File in which statistics are written.
     */
    private StatisticsFile statisticsFile;

    /**
     * {@link List} of settings entries that are created from system properties.
     * Those entries are copied into every {@link ProofCollectionSettings}
     * object. Every system property starting with "key.runallproofs." is
     * considered a RunAllProofs setting. It overrides settings specified in the
     * automaticJAVADL.txt index file. RunAllProofs settings can be specified via
     * system properties by providing JVM arguments like:
     * "-Dkey.runallproofs.forkMode=perFile"
     */
    private static final List<Entry<String, String>> SYSTEM_PROPERTIES_ENTRIES;

    static {
        /*
         * Iterating over all system properties to get settings entries. System
         * properties starting with "key.runallproofs." are relevant for proof
         * collection settings.
         */
        List<Entry<String, String>> tmp = new LinkedList<>();
        Set<Entry<Object, Object>> entrySet = System.getProperties().entrySet();
        for (Entry<Object, Object> entry : entrySet) {
            String key = (String) entry.getKey();
            String value = (String) entry.getValue();
            if (key.startsWith("key.runallproofs.")) {
                key = key.substring(17);// strip "key.runallproofs." from key
                tmp.add(getSettingsEntry(key, value));
            }
        }
        SYSTEM_PROPERTIES_ENTRIES = Collections.unmodifiableList(tmp);
    }

    public ProofCollectionSettings() {
        settings = createUnmodifiableMapContainingDefaults();
    }

    public ProofCollectionSettings(ProofCollectionSettings parent) {
        settings = new HashMap<>(parent.settings);
    }


    /**
     * Converts a list of map entries to an unmodifiable map containing the
     * specified entries and additionally default entries specified in
     * {@link #SYSTEM_PROPERTIES_ENTRIES}.
     */
    private static Map<String, String> createUnmodifiableMapContainingDefaults() {
        Map<String, String> mutableMap = new LinkedHashMap<>();
        /*
         * Add entries created from system properties.
         */
        for (Entry<String, String> entry : SYSTEM_PROPERTIES_ENTRIES) {
            mutableMap.put(entry.getKey(), entry.getValue());
        }
        return mutableMap;
    }


    /**
     * Reads out generic settings, which were be specified as (key, value) pairs
     * during object creation.
     *
     * @see Entry
     */
    public String get(String key) {
        return settings.get(key);
    }

    public ForkMode getForkMode() {
        ForkMode forkMode = null;
        String forkModeString = get(KEY_FORK_MODE);
        if (forkModeString == null || forkModeString.length() == 0) {
            // Return default value in case no particular fork mode is
            // specified.
            forkMode = ForkMode.NOFORK;
        } else {
            for (ForkMode mode : ForkMode.values()) {
                if (mode.settingName.toLowerCase().equals(
                        forkModeString.toLowerCase())) {
                    forkMode = mode;
                    break;
                }
            }
        }

        /*
         * Warn user that specified fork mode was not recognized but use default
         * fork mode rather than throwing an Exception.
         */
        if (forkMode == null) {
            /*
             * Unknown value used for fork mode. Printing out warning to the user.
             */
            System.out
                    .println("Warning: Unknown value used for runAllProofs fork mode: "
                            + forkModeString);
            System.out
                    .println("Use either of the following: noFork (default), perGroup, perFile");
            System.out.println("Using default fork mode: noFork");
            System.out
                    .println("If you want to inspect source code, look up the following location:");
            System.out.println(new Throwable().getStackTrace()[0]);
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
        String lks = get(KEY_LOCAL_SETTINGS);
        return lks;
    }

    public ProofCollectionSettings setLocalKeYSettings(String props) {
        settings.put(KEY_LOCAL_SETTINGS, props);
        return this;
    }

    /**
     * Settings must specify a base directory. Relative
     * {@link ProofCollectionSettings} paths will be treated as relative to
     * directory returned by this method.
     */
    public File getBaseDirectory() {
        String baseDirectoryName = get(KEY_BASE_DIRECTORY);
        if (baseDirectoryName == null) baseDirectoryName = ".";
        return new File(baseDirectoryName).getAbsoluteFile();
    }

    public ProofCollectionSettings setBaseDirectory(String s) {
        settings.put(KEY_BASE_DIRECTORY, new File(s).getAbsolutePath());
        return this;
    }

    /**
     * Returns location of statistics file. Can be null. In this case no
     * statistics are saved.
     */
    public StatisticsFile getStatisticsFile() {
        if (statisticsFile == null) {
            statisticsFile = new StatisticsFile(new File(get(KEY_STATISTICS_FILE)));
        }
        return statisticsFile;
    }

    public File getTempDir() throws IOException {
        String tempDirString = get(KEY_TEMP_DIR);
        if (tempDirString == null) {
            throw new IOException(
                    String.format("No temporary directory specified in RunAllProofs configuration file. " +
                                    "Cannot run in forked mode. To solve this, specify setting \"%s\"",
                            KEY_TEMP_DIR));
        }
        File tempDir = new File(tempDirString);
        if (!tempDir.isAbsolute()) {
            tempDir = new File(getBaseDirectory(), tempDirString);
        }
        if (tempDir.isFile()) {
            throw new IOException("Specified temporary directory is a file: "
                    + tempDir + "\n" + "Configure temporary directory in file to solve this.");
        }
        return tempDir;
    }

    /**
     * Retrieve names of test cases that are configured to be enabled. By
     * default, all {@link RunAllProofsTest} test cases are enabled. If this
     * method returns something else than null, then only test cases whose name
     * is contained in the returned set are enabled.
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
     * Check whether proof reloading is enabled or disabled. If enabled, closed
     * proofs will be saved and reloaded after prover is finished.
     */
    public boolean reloadEnabled() {
        String reloadEnabled = get(KEY_RELOAD_ENABLED);
        if (reloadEnabled == null || reloadEnabled.equals("true")
                || reloadEnabled.equals("")) {
            return true;
        } else if (reloadEnabled.equals("false")) {
            return false;
        } else {
            System.out.println("Warning - unrecognized reload option: "
                    + reloadEnabled);
            System.out.println("To check Java code for this message, see:");
            System.out.println(new Throwable().getStackTrace()[0]);
            return true;
        }
    }

    /**
     * Static method for creation of {@link ProofCollectionSettings} entries.
     */
    public static Entry<String, String> getSettingsEntry(final String key,
                                                         final String value) {
        return new Entry<String, String>() {

            @Override
            public String getKey() {
                return key;
            }

            @Override
            public String getValue() {
                return value;
            }

            @Override
            public String setValue(String value) {
                throw new UnsupportedOperationException(
                        "Proof collection settings are immutable. Changing settings values is not allowed.");
            }
        };
    }

    /**
     * Gets the list of groups on which the test should be run.
     *
     * <code>null</code> means all of them, otherwise a list of group names
     *
     * @return <code>null</code> or a list.
     */
    public List<String> getRunOnlyOn() {
        String runOnly = get(KEY_RUN_ONLY_ON);
        if (runOnly == null) {
            return null;
        } else {
            return Arrays.asList(runOnly.trim().split(" *, *"));
        }
    }

    /**
     * Gets the directory for a group.
     * <p>
     * If the groups has its own directory key, take it into consideration,
     * return the base directory otherwise
     *
     * @return the directory for the current group.
     */
    public File getGroupDirectory() {
        String localDir = get(KEY_DIRECTORY);
        if (localDir != null) {
            return new File(getBaseDirectory(), localDir);
        } else {
            return getBaseDirectory();
        }
    }


    public ProofCollectionSettings setStatisticsFile(String value) {
        settings.put(KEY_STATISTICS_FILE, value);
        return this;
    }

    public ProofCollectionSettings setForkMode(ForkMode mode) {
        settings.put(KEY_FORK_MODE, mode.settingName);
        return this;
    }

    public ProofCollectionSettings setForkTimeout(int timeout) {
        settings.put(KEY_FORK_TIMEOUT, String.valueOf(timeout));
        return this;
    }

    public ProofCollectionSettings setReloadEnabled(boolean value) {
        settings.put(KEY_RELOAD_ENABLED, Boolean.toString(value));
        return this;
    }

    public ProofCollectionSettings setTempDir(String value) {
        settings.put(KEY_TEMP_DIR, new File(value).getAbsolutePath());
        return this;
    }

    public ProofCollectionSettings setKeySettingsFromFile(String filename) {
        throw new RuntimeException("todo");
//        return this;
    }

    public ProofCollectionSettings setVerbose(boolean value) {
        settings.put(KEY_VERBOSE, Boolean.toString(value));
        return this;
    }

    public boolean isVerbose() {
        return Boolean.parseBoolean(get(KEY_VERBOSE));
    }

    public boolean isIgnore() {
        return Boolean.parseBoolean(get(IGNORE_KEY));
    }

    public String getForkDebugPort() {
        return get(FORK_DEBUG_PORT);
    }

    public int getForkTimeout() {
        final String v = get(KEY_FORK_TIMEOUT);
        return v != null ? Integer.parseInt(v) : 100000;
    }

    public String getForkMemory() {
        return get(KEY_FORK_MEMORY);
    }

    public ProofCollectionSettings setForkMemory(int memory) {
        settings.put(KEY_FORK_MEMORY, String.valueOf(memory));
        return this;
    }

    public ProofCollectionSettings setGlobalKeYSettings(String settings) {
        this.settings.put(KEY_SETTINGS_KEY, settings);
        return this;
    }
}
