package de.uka.ilkd.key.util;

import de.uka.ilkd.key.parser.Location;
import org.jetbrains.annotations.Nullable;

import java.net.MalformedURLException;

/**
 * This interface marks classes that provide a location property.
 * <p>
 * The location denotes a position within a file,
 * used e.g., to point at errornous positions.
 *
 * @author Alexander Weigl
 * @version 1 (11/3/20)
 * @see ExceptionTools#getLocation(Throwable)
 */
public interface Locatable {
    /**
     * Returns a location or null.
     *
     * @throws MalformedURLException if the underlying filename could not be parsed as an URL
     */
    @Nullable Location getLocation() throws MalformedURLException;
}
