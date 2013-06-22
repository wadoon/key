package se.gu.svanefalk.testgeneration.frontend.cli;

import java.util.HashMap;

import se.gu.svanefalk.testgeneration.backend.IFrameworkConverter;
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
        CLIResources.COVERAGE_PARSERS.put("statement",
                ICodeCoverageParser.statementCoverageParser);
        CLIResources.COVERAGE_PARSERS.put("branch",
                ICodeCoverageParser.branchCoverageParser);
        CLIResources.COVERAGE_PARSERS.put("condition",
                ICodeCoverageParser.conditionCoverageParser);
        CLIResources.COVERAGE_PARSERS.put("decision",
                ICodeCoverageParser.decisionCoverageParser);
        CLIResources.COVERAGE_PARSERS.put("mcdc",
                ICodeCoverageParser.modifiedConditionDecisionCoverageParser);

        FRAMEWORK_CONVERTERS = new HashMap<>();
        CLIResources.FRAMEWORK_CONVERTERS.put("junit4",
                JUnitConverter.getInstance());
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

    public IFrameworkConverter getFrameworkConverter(final String name) {

        return CLIResources.FRAMEWORK_CONVERTERS.get(name);
    }
}
