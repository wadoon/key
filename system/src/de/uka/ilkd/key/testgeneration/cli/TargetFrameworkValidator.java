package de.uka.ilkd.key.testgeneration.cli;

import java.util.LinkedList;

import com.beust.jcommander.IParameterValidator;
import com.beust.jcommander.ParameterException;

public class TargetFrameworkValidator implements IParameterValidator {
    
    /**
     * Collection which keeps track of the target test frameworks currently supported by KeyTestgen.
     */
    private static final LinkedList<String> legalFrameworks;
    static {
        legalFrameworks = new LinkedList<String>();
        legalFrameworks.add("junit");
    }

    @Override
    public void validate(String parameter, String value) throws ParameterException {

        /*
         * Check that the framework is in the supported set
         */
        if(!legalFrameworks.contains(value)) {
            throw new ParameterException("illegal target framework: " + value);
        }
    }
}