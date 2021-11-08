// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.management.ObjectName;
import java.lang.management.ManagementFactory;

/**
 * {@code Debug} offers some methods for assertions, debug output and so on.
 */
public final class Debug implements DebugMBean {
    private static final Logger LOGGER = LoggerFactory.getLogger(Debug.class);

    /**
     * has to be set in order to enable assertion
     */
    public static boolean ENABLE_ASSERTION =
            Boolean.parseBoolean(System.getProperty("KeyAssertionFlag", "true"));

    /**
     * has to be set in order to enable debugging
     */
    public static boolean ENABLE_DEBUG =
            "on".equals(System.getProperty("KeyDebugFlag"))
                    || "on".equals(System.getenv("KeyDebugFlag"));

    /**
     * Using the command line switch "-Dkey.debug.prefix" one can choose
     * of which classes the debug output is to be send to the standard
     * output.
     * <p>
     * For example:
     * runProver -Dkey.debug.prefix=de.uka.ilkd.key.java,de.uka.ilkd.key.proof.ProblemLoader
     * <p>
     * will display all debug outputs either coming from package de...java
     * (or any subpackage) or from the class ProblemLoader.
     * <p>
     * Stacktraces will always be printed.
     * The colon as splitting character is supported for legacy reasons.
     */
    public static String[] showOnlyPrefixes =
            System.getProperty("key.debug.prefix", "").split("[:,]");

    /**
     * prints given string if in debug mode
     *
     * @param msg the String to be printed
     */
    public static void out(String msg) {
        LOGGER.debug(msg);
        /*if (ENABLE_DEBUG) {
            dbgPrint(msg);
        }*/
    }

    /**
     * prints the given string followed by the stacktrace of the throwable
     * object. If it is null, nothing is printed.
     *
     * @param msg message to be printed
     * @param exc a throwable object
     */
    public static void out(String msg, Throwable exc) {
        LOGGER.debug(msg, exc);
        /*if (ENABLE_DEBUG) {
            dbgPrint(msg);
            if (exc != null)
                exc.printStackTrace(System.out);
        }*/
    }

    /**
     * prints given string and the result of calling the toString method of of
     * the given obj if in debug mode. The advantage of calling the toString
     * here and not before is that if debug mode is disabled no string
     * computation is done
     *
     * @param msg the String to be printed
     * @param obj the Object where to call the toString method
     */
    public static void out(String msg, Object obj) {
        LOGGER.debug(msg + " " + obj);
        /*if (ENABLE_DEBUG) {
            dbgPrint(msg + " " + obj);
        }*/
    }

    /**
     * prints given string and the result of calling the toString method of of
     * the given objects if in debug mode. The advantage of calling the toString
     * here and not before is that if debug mode is disabled no string
     * computation is done
     *
     * @param msg  the String to be printed
     * @param obj1 the first Object where to call the toString method
     * @param obj2 the second Object where to call the toString method
     */
    public static void out(String msg, Object obj1, Object obj2) {
        LOGGER.debug("{}: ({}, {})", msg, obj1, obj2);
        /*if (ENABLE_DEBUG) {
            dbgPrint(msg + ": (" + obj1 + ", " + obj2 + ")");
        }*/
    }

    /**
     * prints given string and the result of calling the toString method of of
     * the given objects if in debug mode. The advantage of calling the toString
     * here and not before is that if debug mode is disabled no string
     * computation is done
     *
     * @param msg  the String to be printed
     * @param obj1 the first Object where to call the toString method
     * @param obj2 the second Object where to call the toString method
     * @param obj3 the third Object where to call the toString method
     */
    public static void out(String msg, Object obj1, Object obj2, Object obj3) {
        LOGGER.debug("{}: ({}, {}, {})", msg, obj1, obj2, obj3);
        /*if (ENABLE_DEBUG) {
            dbgPrint(msg + ": (" + obj1 + ", " + obj2 + ", " + obj3 + ")");
        }*/
    }

    /**
     * prints given string, if the condition cond is true
     *
     * @param msg  the String to be printed
     * @param cond the boolean deciding if the message is printed or not
     */
    public static void outIfEqual(String msg, boolean cond) {
        if (cond) {
            LOGGER.debug(msg);
        }
    }

    /**
     * prints given string, if calling the equal method of obj1, with obj2 as
     * argument results in true
     *
     * @param msg  the String to be printed
     * @param obj1 the Object where to call the equals method
     * @param obj2 the Object given to as parameter of the equals method of obj1
     */
    public static void outIfEqual(String msg, Object obj1, Object obj2) {
        if ((obj1 == null && obj2 == null)
                || (obj1 != null && obj1.equals(obj2))) {
            LOGGER.debug(msg);
        }
    }

    /**
     * prints the stack trace if in debug mode
     *
     * @author VK
     */
    public static void out(Exception e) {
        LOGGER.debug("", e);
    }

    public static void printStackTrace(Throwable e) {
        LOGGER.debug("", e);
    }

    /**
     * an assertion failure is thrown if isOK is evaluated to false
     *
     * @param isOK boolean the assertion that is checked
     */
    public static void assertTrue(boolean isOK) {
        if (ENABLE_ASSERTION) {
            if (!isOK) {
                fail();
            }
        }
    }

    public static void assertFalse(boolean isNotOK) {
        assertTrue(!isNotOK);
    }

    /**
     * an assertion failure is thrown if isOK is evaluated to false the text in
     * message is handed over to this exception
     *
     * @param isOK    boolean the assertion that is checked
     * @param message String describes the failed assertion
     */
    public static void assertTrue(boolean isOK, String message) {
        if (ENABLE_ASSERTION) {
            if (!isOK) {
                fail(message);
            }
        }
    }

    /**
     * an assertion failure is thrown if isOK is evaluated to false the text in
     * message is handed over to this exception
     *
     * @param isOK    boolean the assertion that is checked
     * @param message String describes the failed assertion
     */
    public static void assertTrue(boolean isOK, String message,
                                  Object parameter) {
        if (ENABLE_ASSERTION) {
            if (!isOK) {
                fail(message + ":" + parameter);
            }
        }
    }

    /**
     * an assertion failure is thrown if an iterable object is either null or
     * contains the null element.
     *
     * @param iterable The iterable object to check
     * @param message  String describes the failed assertion
     */
    public static void assertDeepNonNull(Iterable<?> iterable, String message) {
        if (ENABLE_ASSERTION) {
            if (iterable == null)
                fail("Null pointer: " + message);
            for (Object object : iterable) {
                if (object == null) {
                    fail("Null element in collection:" + message);
                }
            }
        }
    }

    public static void assertFalse(boolean isNotOK, String message) {
        assertTrue(!isNotOK, message);
    }

    public static void fail() {
        fail("No further information available.");
    }

    public static void fail(String message) {
        if (ENABLE_ASSERTION) {
            throw new AssertionFailure("\nAssertion failure: " + message);
        }
    }

    public static void fail(String message, Object o) {
        if (ENABLE_ASSERTION) {
            throw new AssertionFailure("\nAssertion failure: " + message + ":"
                    + o);
        }
    }

    /**
     * print a string to stdout, prefixed by the execution context of the caller
     * of the calling function.
     * <p>
     * If {@link #showOnlyPrefixes} is defined, the output is only written, if
     * the caller prefix begins with one of the specified strings
     *
     * @param string string to be printed out
     * @author MU
     */
    private static void dbgPrint(String string) {
        String prefix = getClassAndMethod(3);
        for (String so : showOnlyPrefixes) {
            if (prefix.startsWith(so)) {
                System.out.println("DEBUG in " + prefix + ":: " + string);
                return;
            }
        }
    }

    /**
     * Prints a stack trace (without influencing the execution in any way).
     *
     * @author VK
     */
    public static void printStackTrace() {
        try {
            throw new Exception();
        } catch (Exception e) {
            System.out.println("************* DEBUG::Stacktrace *************");
            e.printStackTrace(System.out);
        }
    }

    public static String stackTrace() {
        Throwable t = new Throwable();
        java.io.ByteArrayOutputStream baos = new java.io.ByteArrayOutputStream();
        t.printStackTrace(new java.io.PrintStream(baos));
        return (baos.toString());
    }

    /**
     * return information about the current execution context (and line number
     * if available) as a string. It the same as in the exception stack traces
     * and composed like
     *
     * <pre>
     *     de.uka.package.ClassName.methodName(ClassName.java:123)
     * </pre>
     * <p>
     * It uses the context of the calling method.
     *
     * @return a String giving information about the stack of the calling
     * function.
     * @author MU
     */
    public static String getClassAndMethod() {
        return getClassAndMethod(1);
    }

    /**
     * return information about some execution context. The context of interest
     * may have appeared several levels higher.
     *
     * @param level to go up in the context hierarchy
     * @return a String giving information about the stack of the calling
     * function.
     * @author MU
     */
    private static String getClassAndMethod(int level) {
        StackTraceElement[] trace = new Exception().getStackTrace();
        if (trace.length > level) {
            return trace[level].toString();
        }
        return "";
    }

    //	
    // Management functionality. Allows to set debug parameters dynamically using the JMX interface
    //
    // There are two setters and two getters to get and set the 
    // debug related static flags in this class. An instance of
    // this class is created and registered with a MBeanServer.
    // It provides now an interface to set the debug parameters
    // at runtime using for instance "jconsole".

    public void setDebugState(boolean debug) {
        Debug.ENABLE_DEBUG = debug;
    }

    public boolean getDebugState() {
        return Debug.ENABLE_DEBUG;
    }

    static {
        try {
            ManagementFactory.getPlatformMBeanServer().registerMBean(
                    new Debug(), new ObjectName("de.uka.ilkd.key:Type=Debug"));
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    public String getShowOnlyPrefixes() {
        StringBuilder sb = new StringBuilder();
        for (String s : showOnlyPrefixes) {
            sb.append(s).append(":");
        }
        sb.deleteCharAt(sb.length() - 1);
        return sb.toString();
    }

    public void setShowOnlyPrefixes(String showOnlyPrefixes) {
        Debug.showOnlyPrefixes = showOnlyPrefixes.split(":");
    }


    //	
    // Methods mimicking the log4j interface
    // (TODO: provide fuller implementation of this interface)
    //

    public static void log4jDebug(String msg, String loggerID) {
        out(msg);
    }


    public static void log4jInfo(String msg, String loggerID) {
        out(msg);
    }

    public static void log4jWarn(String msg, String loggerID) {
        out(msg);
    }

    public static void log4jError(String msg, String loggerID) {
        out(msg);
    }

}