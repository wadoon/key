package se.gu.svanefalk.testgeneration.frontend.cli;

import java.util.HashMap;

import se.gu.svanefalk.testgeneration.backend.custom.ITestCaseParser;
import se.gu.svanefalk.testgeneration.core.NodeTestGenerator;

/**
 * Shared resources for the KeyTestGen CLI.
 * 
 * @author christopher
 */
public class CLIResources {
    
    private static CLIResources instance = null;

    public static CLIResources getInstance() {
        if (instance == null) {
            instance = new CLIResources();
        }
        return instance;
    }

    private CLIResources() {

    }

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
