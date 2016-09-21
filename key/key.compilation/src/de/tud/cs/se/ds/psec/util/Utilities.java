package de.tud.cs.se.ds.psec.util;

import java.util.stream.Stream;
import java.util.stream.StreamSupport;

/**
 * Miscellaneous utilities container class.
 *
 * @author Dominic Scheurer
 */
public class Utilities {

    /**
     * Converts the given {@link Iterable} to a {@link Stream}.<br/>
     * TODO is this method needed? Currently seems to be unused.
     * 
     * @param it The {@link Iterable} to convert to a {@link Stream}.
     * @return The {@link Stream} for the given {@link Iterable}.
     */
    public static <T> Stream<T> toStream(Iterable<T> it) {
        return StreamSupport.stream(it.spliterator(), false);
    }

}
