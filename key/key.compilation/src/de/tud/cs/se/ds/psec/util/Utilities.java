package de.tud.cs.se.ds.psec.util;

import java.io.File;
import java.io.IOException;
import java.nio.file.FileVisitOption;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Miscellaneous utilities container class.
 *
 * @author Dominic Scheurer
 */
public class Utilities {
    private static final Logger logger = LogManager.getFormatterLogger();

    /**
     * Converts the given {@link Iterable} to a {@link Stream}.<br/>
     * TODO is this method needed? Currently seems to be unused.
     * 
     * @param it
     *            The {@link Iterable} to convert to a {@link Stream}.
     * @return The {@link Stream} for the given {@link Iterable}.
     */
    public static <T> Stream<T> toStream(Iterable<T> it) {
        return StreamSupport.stream(it.spliterator(), false);
    }

    /**
     * Recursively deletes the given path.
     * 
     * @param pathToDirectory
     *            The path to delete.
     * @return true iff the deletion was successful, i.e. no exception has been
     *         thrown.
     */
    public static boolean recursivelyRemoveFiles(Path pathToDirectory) {
        try {
            logger.trace("Recursively deleting %s", pathToDirectory);
            Files.walk(pathToDirectory, FileVisitOption.FOLLOW_LINKS)
                    // Reverse sorting to obtain the recursive order
                    .sorted(Comparator.reverseOrder())
                    // Map map to file
                    .map(Path::toFile)
                    // Output which file is being processed
                    .peek(logger::trace)
                    // Then delete the file(s)
                    .forEach(File::delete);
        }
        catch (IOException e) {
            logger.error("Problem during deleting resource / directory %s:\n%s",
                    pathToDirectory, e.toString());
            return false;
        }

        return true;
    }

}
