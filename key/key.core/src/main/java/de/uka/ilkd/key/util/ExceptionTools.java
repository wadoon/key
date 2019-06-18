package de.uka.ilkd.key.util;

import de.uka.ilkd.key.parser.KeYSemanticException;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.proofjava.ParseException;
import de.uka.ilkd.key.parser.proofjava.Token;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import org.antlr.runtime.RecognitionException;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

/**
 * Various utility methods related to exceptions.
 *
 * @author bruns
 * @since 2.4.0
 */
public final class ExceptionTools {
    /**
     * Tries to resolve the location (i.e., file name, line, and column) from a given (parsing) exception.
     * <p>
     * First, it is checked whether the exception implements the {@link Locatable} interface. This is the preferred
     * variant for extended this functionality.
     * <p>
     * Second, this method contains special treatment for <i>external</i>-defined exceptions: {@link RecognitionException}
     * and {@link ParseException} from Antlr and JavaCC.
     * <p>
     * Third, the method follows the causes ({@link Throwable#getCause}).
     *
     * @author weigl
     * @see Locatable
     */
    public static @Nullable Location getLocation(@NotNull Throwable exc) {
        assert exc != null;
        try {
            Locatable locatable = (Locatable) exc;
            return locatable.getLocation();
        } catch (ClassCastException ignored) {
        }

        if (exc instanceof RecognitionException) {
            RecognitionException recEx = (RecognitionException) exc;
            if (recEx.input != null) {
                // ANTLR has 0-based column numbers, hence +1.
                return new Location(recEx.input.getSourceName(),
                        recEx.line, recEx.charPositionInLine + 1);
            }
        }

        if (exc instanceof ParseException) {
            ParseException pexc = (ParseException) exc;
            Token token = pexc.currentToken;
            if (token == null) {
                return null;
            } else {
                // JavaCC has 1-based column numbers
                return new Location("", token.next.beginLine, token.next.beginColumn);
            }
        }

        if (exc.getCause() != null) {
            return getLocation(exc.getCause());
        }

        return null;
    }

    private static Location getLocation(RecognitionException exc) {
        Location location = null;
        // ANTLR 3 - Recognition Exception.
        if (exc instanceof SLTranslationException) {
            SLTranslationException ste = (SLTranslationException) exc;
            location = new Location(ste.getFileName(),
                    ste.getLine(),
                    ste.getColumn());
        } else if (exc instanceof KeYSemanticException) {
            KeYSemanticException kse = (KeYSemanticException) exc;
            // ANTLR has 0-based column numbers, hence +1.
            location = new Location(kse.getFilename(), kse.getLine(), kse.getColumn() + 1);
        } else if (recEx.input != null) {
            // ANTLR has 0-based column numbers, hence +1.
            location = new Location(recEx.input.getSourceName(),
                    recEx.line, recEx.charPositionInLine + 1);
        }
        return location;
    }

}
