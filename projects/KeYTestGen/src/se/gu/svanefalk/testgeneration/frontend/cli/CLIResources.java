package se.gu.svanefalk.testgeneration.frontend.cli;

import java.util.HashMap;

import se.gu.svanefalk.testgeneration.backend.IFrameworkConverter;
import se.gu.svanefalk.testgeneration.backend.custom.ITestCaseParser;
import se.gu.svanefalk.testgeneration.backend.junit.JUnitConverter;
import se.gu.svanefalk.testgeneration.core.codecoverage.ICodeCoverageParser;

/**
 * Shared resources for the KeyTestGen CLI.
 * 
 * @author christopher
 */
public class CLIResources {

    /**
     * Collection which keeps track of the target test COVERAGE_PARSERS
     * currently supported by KeyTestgen, together with their parsers.
     */
    private static final HashMap<String, ICodeCoverageParser> COVERAGE_PARSERS;

    private static final HashMap<String, IFrameworkConverter> FRAMEWORK_CONVERTERS;

    private static CLIResources instance = null;

    static {
        COVERAGE_PARSERS = new HashMap<>();
        COVERAGE_PARSERS.put("statement",
                ICodeCoverageParser.statementCoverageParser);
        COVERAGE_PARSERS.put("branch", ICodeCoverageParser.branchCoverageParser);
        COVERAGE_PARSERS.put("condition",
                ICodeCoverageParser.conditionCoverageParser);
        COVERAGE_PARSERS.put("decision",
                ICodeCoverageParser.decisionCoverageParser);
        COVERAGE_PARSERS.put("mcdc",
                ICodeCoverageParser.modifiedConditionDecisionCoverageParser);

        FRAMEWORK_CONVERTERS = new HashMap<>();
        FRAMEWORK_CONVERTERS.put("junit4", JUnitConverter.getInstance());
    }

    public static CLIResources getInstance() {
        if (CLIResources.instance == null) {
            CLIResources.instance = new CLIResources();
        }
        return CLIResources.instance;
    }

    private CLIResources() {

    }

    public ICodeCoverageParser getCodeCoverageParser(final String framework) {

        return CLIResources.COVERAGE_PARSERS.get(framework);
    }

    public IFrameworkConverter getFrameworkConverter(String name) {

        return FRAMEWORK_CONVERTERS.get(name);
    }
}
