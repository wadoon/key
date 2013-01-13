package de.uka.ilkd.key.testgeneration.cli;

import java.util.LinkedList;

import com.beust.jcommander.IParameterValidator;
import com.beust.jcommander.ParameterException;

public class TargetFrameworkValidator implements IParameterValidator {

    @Override
    public void validate(String parameter, String value) throws ParameterException {

        /*
         * Check that the framework is in the supported set
         */
        if(!CLIResources.INSTANCE.isSupportedFramework(value)) {
            throw new ParameterException("illegal target framework: " + value);
        }
    }
}