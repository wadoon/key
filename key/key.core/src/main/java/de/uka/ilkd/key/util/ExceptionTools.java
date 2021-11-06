package de.uka.ilkd.key.util;

import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.parsing.HasLocation;
import org.antlr.runtime.RecognitionException;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.net.MalformedURLException;

/**
 * Various utility methods related to exceptions.
 *
 * @author bruns
 * @since 2.4.0
 */
public final class ExceptionTools {

    private ExceptionTools() {
    }

    /**
     * Tries to resolve the location (i.e., file name, line, and column)
     * from a parsing exception.
     * Result may be null.
     *
     * @param exc the Throwable to extract the Location from
     * @return the Location stored inside the Throwable or null if no such can be found
     * @throws MalformedURLException if the no URL can be parsed from the String stored
     *                               inside the given Throwable can not be successfully converted to a URL and thus
     *                               no Location can be created
     */
    @Nullable
    public static Location getLocation(@Nonnull Throwable exc) throws MalformedURLException {
        Location location = null;
        if (exc instanceof HasLocation) {
            return ((HasLocation) exc).getLocation();
        } else if (exc instanceof RecognitionException) {
            location = getLocation((RecognitionException) exc);
        }

        if (location == null && exc.getCause() != null) {
            location = getLocation(exc.getCause());
        }
        return location;
    }


    @Nullable
    private static Location getLocation(RecognitionException exc) throws MalformedURLException {
        // ANTLR 3 - Recognition Exception.
        if (exc.input != null) {
            // ANTLR has 0-based column numbers, hence +1.
            return new Location(exc.input.getSourceName(), exc.line, exc.charPositionInLine + 1);
        }
        return null;
    }

}
