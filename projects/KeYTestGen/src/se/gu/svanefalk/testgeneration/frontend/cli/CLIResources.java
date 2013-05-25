package se.gu.svanefalk.testgeneration.frontend.cli;

import java.util.HashMap;

import se.gu.svanefalk.testgeneration.backend.custom.ITestCaseParser;

/**
 * Shared resources for the KeyTestGen CLI.
 * 
 * @author christopher
 */
public class CLIResources {

    /**
     * Collection which keeps track of the target test FRAMEWORKS currently
     * supported by KeyTestgen, together with their parsers.
     */
    private static final HashMap<String, ITestCaseParser<String>> FRAMEWORKS;

    private static CLIResources instance = null;

    static {
        FRAMEWORKS = new HashMap<String, ITestCaseParser<String>>();
    }

    public static CLIResources getInstance() {
        if (CLIResources.instance == null) {
            CLIResources.instance = new CLIResources();
        }
        return CLIResources.instance;
    }

    private CLIResources() {

    }

    public ITestCaseParser<String> getFrameworkParser(final String framework) {

        return CLIResources.FRAMEWORKS.get(framework);
    }

    public boolean isSupportedFramework(final String framework) {

        return CLIResources.FRAMEWORKS.containsKey(framework);
    }
}
