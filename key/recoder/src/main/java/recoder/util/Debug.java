package recoder.util;

import java.io.*;
import java.util.Properties;

public class Debug {
    protected static final String[] NEGATIVE_VALUES = new String[]{"", "0", "false", "off", "no", "none"};
    protected static final String DEBUGGING_OPTION_FILE = "debug.properties";
    static final String ESC_PREFIX = "\033[3;31m";
    static final String ESC_SUFFIX = "\033[0m";
    protected static int level = 1;
    protected static PrintStream output = System.err;
    static String ERROR_MESSAGE = "Error: ";
    static String RESTRICTION_MESSAGE = "Restriction: ";
    static String INFO_MESSAGE = "Info: ";
    static String ASSERTION_MESSAGE = "Assertion failed: ";
    private static Properties debuggingOptions = null;

    protected static Properties getDebuggingOptions() {
        if (debuggingOptions == null) {
            debuggingOptions = new Properties();
            try {
                debuggingOptions.load(new FileInputStream("debug.properties"));
            } catch (IOException ioe) {
            }
        }
        return debuggingOptions;
    }

    protected static boolean isSet(Properties prop, String key) {
        String value = prop.getProperty(key);
        if (value == null)
            return false;
        for (int i = 0; i < NEGATIVE_VALUES.length; i++) {
            if (NEGATIVE_VALUES[i].equalsIgnoreCase(value))
                return false;
        }
        return true;
    }

    public static boolean isSet(String key) {
        return isSet(getDebuggingOptions(), key);
    }

    public static int getLevel() {
        return level;
    }

    public static void setLevel(int level) {
        Debug.level = level;
    }

    public static void setOutput(PrintStream s) {
        if (s == null)
            throw new NullPointerException();
        output = s;
    }

    public static void println(String option, String printoutString) {
        if (isSet(getDebuggingOptions(), option))
            System.out.println(printoutString);
    }

    public static void printlno(String option, String printoutString) {
        if (isSet(getDebuggingOptions(), option))
            System.out.println("Option " + option + ":" + printoutString);
    }

    public static void setOption(String key, String value) {
        getDebuggingOptions().put(key, value);
    }

    public static void error(String error) {
        if (isSet("terminal.escapes")) {
            output.println("\033[3;31m" + ERROR_MESSAGE + "\033[0m" + error);
        } else {
            output.println(ERROR_MESSAGE + error);
        }
    }

    public static void restriction(String restriction) {
        output.println(RESTRICTION_MESSAGE + restriction);
    }

    public static void log(String info) {
        output.println(info);
    }

    public static void info(String info) {
        output.println(INFO_MESSAGE + info);
    }

    public static void info(int level, String info) {
        if (Debug.level >= level)
            output.println(INFO_MESSAGE + info);
    }

    public static final void assertBoolean(boolean expression) {
        if (!expression)
            throw new IllegalStateException(ASSERTION_MESSAGE + "(general condition)");
    }

    public static final void assertBoolean(boolean expression, String message) {
        if (!expression)
            throw new IllegalStateException(ASSERTION_MESSAGE + message);
    }

    public static final void assertNonnull(Object nonnull) {
        if (nonnull == null)
            throw new NullPointerException(ASSERTION_MESSAGE + "(Null object)" + "\n");
    }

    public static final void assertNonnull(Object nonnull1, Object nonnull2) {
        if (nonnull1 == null)
            throw new NullPointerException(ASSERTION_MESSAGE + "(Null object 1)" + "\n");
        if (nonnull2 == null)
            throw new NullPointerException(ASSERTION_MESSAGE + "(Null object 2)" + "\n");
    }

    public static final void assertNonnull(Object nonnull1, Object nonnull2, Object nonnull3) {
        if (nonnull1 == null)
            throw new NullPointerException(ASSERTION_MESSAGE + "(Null object 1)" + "\n");
        if (nonnull2 == null)
            throw new NullPointerException(ASSERTION_MESSAGE + "(Null object 2)" + "\n");
        if (nonnull3 == null)
            throw new NullPointerException(ASSERTION_MESSAGE + "(Null object 3)" + "\n");
    }

    public static final void assertNonnull(Object nonnull1, Object nonnull2, Object nonnull3, Object nonnull4) {
        if (nonnull1 == null)
            throw new NullPointerException(ASSERTION_MESSAGE + "(Null object 1)" + "\n");
        if (nonnull2 == null)
            throw new NullPointerException(ASSERTION_MESSAGE + "(Null object 2)" + "\n");
        if (nonnull3 == null)
            throw new NullPointerException(ASSERTION_MESSAGE + "(Null object 3)" + "\n");
        if (nonnull4 == null)
            throw new NullPointerException(ASSERTION_MESSAGE + "(Null object 4)" + "\n");
    }

    public static final void assertNonnull(Object nonnull, String message) {
        if (nonnull == null)
            throw new NullPointerException(ASSERTION_MESSAGE + message);
    }

    public static final String makeStackTrace() {
        StringWriter buf = new StringWriter();
        try {
            throw new RuntimeException();
        } catch (RuntimeException e) {
            e.printStackTrace(new PrintWriter(buf));
            buf.flush();
            String str = buf.toString();
            int begin = str.indexOf('\n', str.indexOf('\n') + 1) + 1;
            return str.substring(begin, str.lastIndexOf('\n'));
        }
    }

    public static final long getUsedMemory() {
        Runtime run = Runtime.getRuntime();
        long totalMem = run.totalMemory();
        long freeMem = run.freeMemory();
        while (true) {
            run.gc();
            long oldFreeMem = freeMem;
            freeMem = run.freeMemory();
            if (freeMem <= oldFreeMem + 256L)
                return totalMem - freeMem;
        }
    }
}
