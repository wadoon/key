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
     * TODO
     * 
     * @param it
     * @return
     */
    public static <T> Stream<T> toStream(Iterable<T> it) {
        return StreamSupport.stream(it.spliterator(), false);
    }

}
