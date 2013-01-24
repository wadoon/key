package de.uka.ilkd.key.testgeneration.frontend.cli;

import java.util.HashMap;

import de.uka.ilkd.key.testgeneration.xmlparser.ITestCaseParser;
import de.uka.ilkd.key.testgeneration.xmlparser.junitparser.JUnitParser;

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
        FRAMEWORKS.put("junit", JUnitParser.getInstance());
    }

    public boolean isSupportedFramework(String framework) {

        return FRAMEWORKS.containsKey(framework);
    }

    public ITestCaseParser<String> getFrameworkParser(String framework) {

        return FRAMEWORKS.get(framework);
    }
}
