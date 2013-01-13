package de.uka.ilkd.key.testgeneration.cli;

import java.io.File;
import java.util.Scanner;

import com.beust.jcommander.IStringConverter;
import com.sun.xml.internal.stream.Entity.ScannedEntity;

/**
 * Instances of this class are used in order to covert between filepaths and actual file streams.
 * 
 * @author christopher
 */
public class JavaFileConverter
        implements IStringConverter<File> {

    @Override
    public File convert(String path) {

        return new File(path);
    }
}
