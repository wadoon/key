package de.uka.ilkd.key.java;

import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.ExceptionTools;
import de.uka.ilkd.key.util.Locatable;
import org.jetbrains.annotations.Nullable;
import recoder.parser.ParseException;

/**
 * This exception extends recoder's {@link ParseException} by a filename.
 * <p>
 * The filename is used to display the location of an error in the sources. Line
 * and column number are not stored here explicitly but retrieved from the
 * cause.
 *
 * @author mulbrich
 */
@SuppressWarnings("serial")
public class ParseExceptionInFile extends ParseException implements Locatable {

    private final String filename;

    public ParseExceptionInFile(String filename, String message, Throwable cause) {
        super("Error in file " + filename + ": " + message);
        this.filename = filename;
        initCause(cause);
    }

    public ParseExceptionInFile(String filename, Throwable cause) {
        this(filename, cause.getMessage(), cause);
    }

    public String getFilename() {
        return filename;
    }

    @Override
    public @Nullable Location getLocation() {
        // This kind of exception has a filename but no line/col information
        // Retrieve the latter from the cause. location remains null if
        // no line/col is available in cause.
        int line = -1, col = -1;
        if (getCause() != null) {
            Location location = ExceptionTools.getLocation(getCause());
            line = location.getLine();
            col = location.getColumn();
        }
        return new Location(getFilename(), line, col);

    }
}
