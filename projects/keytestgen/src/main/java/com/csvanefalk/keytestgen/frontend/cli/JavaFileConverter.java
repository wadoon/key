package com.csvanefalk.keytestgen.frontend.cli;

import com.beust.jcommander.IStringConverter;

import java.io.File;

/**
 * Instances of this class are used in order to covert between filepaths and
 * actual file streams.
 *
 * @author christopher
 */
public class JavaFileConverter implements IStringConverter<File> {

    @Override
    public File convert(final String path) {

        return new File(path);
    }
}
