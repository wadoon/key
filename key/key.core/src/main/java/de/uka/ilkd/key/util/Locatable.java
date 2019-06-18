package de.uka.ilkd.key.util;

import de.uka.ilkd.key.parser.Location;
import org.jetbrains.annotations.Nullable;

/**
 * This interface describes an object which has a location (file and position).
 *
 * @author Alexander Weigl
 * @version 1 (18.06.19)
 * @see Location
 */
public interface Locatable {
    /**
     * Tries to resolve the location (i.e., file name, line, and column), e.g. from a parsing exception.
     *
     * @return null if no location could be determined.
     */
    @Nullable
    Location getLocation();
}
