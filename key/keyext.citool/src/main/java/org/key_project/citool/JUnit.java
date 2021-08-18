package org.key_project.citool;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.Map;

public class JUnit {
    public static class XmlWriter {
        final Writer stream;

        public XmlWriter(Writer stream) {
            this.stream = stream;
        }

        void write(String s, Object... args) {
            try {
                stream.write(String.format(s, args));
            } catch (IOException ignore) {
            }
        }


        void attr(String key, Object value) {
            if (value != null) {
                write(" %s = \"%s\"", key, value);
            }
        }

        void element(String s,
                     Runnable run,
                     Object... attrs) {
            write("<%s", s);
            for (int i = 0; i < attrs.length; i += 2) {
                attr(attrs[i].toString(), attrs[i + 1]);
            }
            write(">");
            if (run != null) run.run();
            write("</%s>", s);
        }

        void cdata(String it) {
            try {
                stream.write("<![CDATA[");
                stream.write(it);
                stream.write("]]>");
            } catch (IOException ignore) {

            }
        }
    }

    public static class TestSuites extends ArrayList<TestSuite> {
        public String name;

        /**
         * total number of successful tests from all testsuites.
         */
        long tests() {
            return stream().mapToLong(ArrayList::size).sum();
        }

        /**
         * total number of disabled tests from all testsuites.
         */
        long disabled() {
            return stream().mapToLong(TestSuite::disabled).sum();
        }

        /**
         * total number of tests with error result from all testsuites.
         */
        long errors() {
            return stream().mapToLong(TestSuite::errors).sum();
        }

        /**
         * total number of failed tests from all testsuites.
         */
        long failures() {
            return stream().mapToLong(TestSuite::failures).sum();
        }

        /**
         * time in seconds to execute all test suites.
         *
         * @return
         */
        double time() {
            return stream().mapToDouble(TestSuite::time).sum();
        }

        public void writeXml(Writer writer) {
            writeXml(new XmlWriter(writer));
        }

        public void writeXml(XmlWriter writer) {
            writer.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>");
            writer.element("testsuites",
                    () -> forEach(it -> it.writeXml(writer)),
                    "errors", errors(),
                    "disabled", disabled(),
                    "failures", failures(),
                    "tests", tests(),
                    "time", time());
        }


        public TestSuite newTestSuite(String name) {
            var ts = new TestSuite(name);
            add(ts);
            return ts;
        }
    }

    public static class TestSuite extends ArrayList<TestCase> {
        /**
         * Full (class) name of the test for non-aggregated testsuite documents.
         * Class name without the package for aggregated testsuites documents. Required
         */
        @Nonnull
        public String name = "";

        public TestSuite(String name) {
            this.name = name;
        }

        /**
         * The total number of tests in the suite, required.
         */
        public int tests() {
            return size();
        }

        /**
         * the total number of disabled tests in the suite. optional
         */
        long disabled() {
            return stream().filter(TestCase::disabled).count();
        }

        /**
         * The total number of tests in the suite that errored. An errored test is one that had an unanticipated problem,
         * for example an unchecked throwable; or a problem with the implementation of the test. optional
         *
         * @return
         */
        long errors() {
            return stream().filter(TestCase::errors).count();

        }

        /**
         * The total number of tests in the suite that failed. A failure is a test which the code has explicitly failed
         * by using the mechanisms for that purpose. e.g., via an assertEquals. optional
         *
         * @return
         */
        long failures() {
            return stream().filter(TestCase::failures).count();
        }

        /**
         * Host on which the tests were executed. 'localhost' should be used if the hostname cannot be determined. optional
         */
        String hostname = "localhost";

        // /** Starts at 0 for the first testsuite and is incremented by 1 for each following testsuite */
        // var id : Int = 0

        /**
         * Derived from testsuite/@name in the non-aggregated documents. optional
         */
        String package_ = "";

        /**
         * The total number of skipped tests. optional
         */
        int skipped() {
            return 0;
        }

        /**
         * Time taken (in seconds) to execute the tests in the suite. optional
         */
        double time() {
            return 0D;
        }

        void writeXml(XmlWriter writer) {
            writer.element("testsuites",
                    () -> {
                        writer.element("properties", () ->
                                properties.forEach((k, v) ->
                                        writer.element("property", EMPTY_BLOCK,
                                                "name", k, "value", v.toString())
                                ));
                        forEach(it -> it.writeXml(writer));
                    },
                    "errors", errors(),
                    "disabled", disabled(),
                    "failures", failures(),
                    "tests", tests(),
                    "hostname", hostname,
                    "package", package_,
                    "skipped", skipped(),
                    "timestamp", timestamp,
                    "time", time());
        }

        public TestCase newTestCase(String name) {
            var tc = new TestCase(name);
            add(tc);
            return tc;
        }

        /**
         * when the test was executed in ISO 8601 format (2014-01-21T16:17:18). Timezone may not be specified. optional
         */
        @Nullable
        public String timestamp = new Date().toString();


        /**
         * property can appear multiple times. The name and value attributres are required.
         */
        Map<String, Object> properties = new HashMap<>();
    }

    public static class TestCase {
        /**
         * Name of the test method, required.
         */
        public String name;

        public TestCase(String name) {
            this.name = name;
        }

        /**
         * Full class name for the class the test method is in. required
         */
        public String classname = "";

        /**
         * number of assertions in the test case. optional
         */
        @Nullable
        public Integer assertions = null;

        /**
         * Time taken (in seconds) to execute the test. optional
         */
        @Nullable
        public Integer time = null;

        /**
         * Unknown
         */
        @Nullable
        public String status = null;

        @Nonnull
        public TestCaseKind result = TestCaseKind.UNKNOWN;

        /**
         * Data that was written to standard out while the test suite was executed. optional
         */
        @Nullable
        String sysout;

        /**
         * Data that was written to standard error while the test suite was executed. optional
         */
        @Nullable
        String syserr;

        boolean disabled() {
            return result instanceof TestCaseKind.Skipped;
        }

        boolean failures() {
            return result instanceof TestCaseKind.Failure;
        }

        boolean errors() {
            return result instanceof TestCaseKind.Error;
        }

        public void writeXml(XmlWriter writer) {
            writer.element("testcase",
                    () -> {
                        result.writeXml(writer);
                        if (syserr != null) {
                            writer.element("system-err",
                                    () -> writer.cdata(syserr));
                        }
                        if (sysout != null) {
                            writer.element("system-out",
                                    () -> writer.cdata(sysout));
                        }
                    },
                    "name", name,
                    "assertions", assertions,
                    "classname", classname,
                    "status", status,
                    "time", time);

        }
    }

    private static final Runnable EMPTY_BLOCK = () -> {
    };


    public static abstract class TestCaseKind {
        abstract void writeXml(XmlWriter writer);

        public final static TestCaseKind UNKNOWN = new TestCaseKind() {
            @Override
            void writeXml(XmlWriter writer) {
            }
        };

        /**
         * If the test was not executed or failed, you can specify one
         * the skipped, error or failure elements.
         * skipped can appear 0 or once. optional
         * message/description string why the test case was skipped. optional
         */
        public static class Skipped extends TestCaseKind {
            final String message;

            public Skipped(String message) {
                this.message = message;
            }

            void writeXml(XmlWriter writer) {
                writer.element("skipped", EMPTY_BLOCK, "message", message);
            }
        }

        /**
         * Indicates that the test errored. An errored test is one
         * that had an unanticipated problem. For example an unchecked
         * throwable or a problem with the implementation of the
         * test. Contains as a text node relevant data for the error,
         * for example a stack trace. optional
         */
        public static class Error extends TestCaseKind {
            /**
             * The error message. e.g., if a java exception is thrown, the return value of getMessage()
             */
            @Nullable
            final String message;
            /**
             * full class name of the exception
             */
            @Nullable
            final String type;

            public Error(@Nullable String message, @Nullable String type) {
                this.message = message;
                this.type = type;
            }

            void writeXml(XmlWriter writer) {
                writer.element("error", EMPTY_BLOCK, "message", message, "type", type);
            }
        }

        /**
         * Indicates that the test failed. A failure is a test which
         * the code has explicitly failed by using the mechanisms for
         * that purpose. For example via an assertEquals. Contains as
         * a text node relevant data for the failure, e.g., a stack
         * trace. optional
         */
        public static class Failure extends TestCaseKind {
            /**
             * The message specified in the assert.
             */
            @Nullable
            final String message;
            /**
             * The type of the assert.
             */
            @Nullable
            final String type;

            public Failure(@Nullable String message, @Nullable String type) {
                this.message = message;
                this.type = type;
            }

            void writeXml(XmlWriter writer) {
                writer.element("failure", null, "message", message);
            }
        }
    }
}