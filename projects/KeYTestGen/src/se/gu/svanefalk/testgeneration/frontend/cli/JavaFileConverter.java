package se.gu.svanefalk.testgeneration.frontend.cli;

import java.io.File;

import com.beust.jcommander.IStringConverter;

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
