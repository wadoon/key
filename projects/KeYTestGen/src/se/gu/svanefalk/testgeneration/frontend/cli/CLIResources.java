package se.gu.svanefalk.testgeneration.frontend.cli;

import java.util.HashMap;

import se.gu.svanefalk.testgeneration.backend.custom.ITestCaseParser;

/**
 * Shared resources for the KeyTestGen CLI.
 * 
 * @author christopher
 */
public enum CLIResources {
    INSTANCE;

    /**
     * Collection which keeps track of the target test FRAMEWORKS currently
     * supported by KeyTestgen, together with their parsers.
     */
    private static final HashMap<String, ITestCaseParser<String>> FRAMEWORKS;
    static {
        FRAMEWORKS = new HashMap<String, ITestCaseParser<String>>();
    }

    public ITestCaseParser<String> getFrameworkParser(final String framework) {

        return CLIResources.FRAMEWORKS.get(framework);
    }

    public boolean isSupportedFramework(final String framework) {

        return CLIResources.FRAMEWORKS.containsKey(framework);
    }
}
