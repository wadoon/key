package se.gu.svanefalk.testgeneration.frontend.cli;

import com.beust.jcommander.IParameterValidator;
import com.beust.jcommander.ParameterException;

public class TargetFrameworkValidator implements IParameterValidator {

    @Override
    public void validate(final String parameter, final String value)
            throws ParameterException {

        /*
         * Check that the framework is in the supported set
         */
        if (!CLIResources.getInstance().isSupportedFramework(value)) {
            throw new ParameterException("illegal target framework: " + value);
        }
    }
}