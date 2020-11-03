package de.uka.ilkd.key.util;

import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.proofjava.ParseException;
import de.uka.ilkd.key.parser.proofjava.Token;
import org.antlr.runtime.RecognitionException;

import java.net.MalformedURLException;

/**
 * Various utility methods related to exceptions.
 *
 * @author bruns
 * @since 2.4.0
 */
public final class ExceptionTools {
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
    public static Location getLocation(Throwable exc) throws MalformedURLException {
        assert exc != null;

        if (exc instanceof Locatable) {
            return ((Locatable) exc).getLocation();
        }
        Location location = null;
        if (exc instanceof RecognitionException) {
            RecognitionException recEx = (RecognitionException) exc;
            // ANTLR 3 - Recognition Exception.
            if (recEx.input != null) {
                // ANTLR has 0-based column numbers, hence +1.
                return new Location(recEx.input.getSourceName(), recEx.line, recEx.charPositionInLine + 1);
            }
        } else if (exc instanceof ParseException) {
            ParseException pexc = (ParseException) exc;
            Token token = pexc.currentToken;
            if (token != null) {
                // JavaCC has 1-based column numbers
                return new Location("", token.next.beginLine, token.next.beginColumn);
            }
        }

        if (exc.getCause() != null) {
            return getLocation(exc.getCause());
        }

        return null;
    }

}
