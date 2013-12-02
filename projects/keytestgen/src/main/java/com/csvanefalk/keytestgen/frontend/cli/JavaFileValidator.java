package com.csvanefalk.keytestgen.frontend.cli;

import com.beust.jcommander.IParameterValidator;
import com.beust.jcommander.ParameterException;

import java.io.File;

/**
 * Instances of this class are used in order to validate Java files.
 *
 * @author christopher
 */
public class JavaFileValidator implements IParameterValidator {

    @Override
    public void validate(final String parameter, final String value)
            throws ParameterException {

        /*
         * Check that the filename is properly prefixed
         */
        if (!value.endsWith(".java")) {
            throw new ParameterException("not a Java source file: " + value);
        }

        /*
         * Check that the file exists
         */
        final File file = new File(value);
        if (!file.exists()) {
            throw new ParameterException("no such file: " + value);
        }
    }
}
